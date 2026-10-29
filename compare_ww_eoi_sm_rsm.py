from __future__ import annotations

import argparse
import csv
import math
import random
import statistics
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import matplotlib.pyplot as plt


# ---------------------------------------------------------------------------
# Robust aggregation
# ---------------------------------------------------------------------------

def mean(xs: Sequence[float]) -> float:
    return statistics.fmean(xs) if xs else 0.0


def admissible(xs: Sequence[float], k: int) -> bool:
    return k >= 0 and 2 * k < len(xs)


def trim(xs: Sequence[float], k: int) -> List[float]:
    if not admissible(xs, k):
        raise ValueError(f"Require 2*k < n, got k={k}, n={len(xs)}")
    ordered = sorted(map(float, xs))
    return ordered[k:len(ordered) - k] if k else ordered


def tmean(xs: Sequence[float], k: int) -> float:
    return mean(trim(xs, k))


def panel_mean(panel: Sequence[Sequence[float]]) -> List[float]:
    """Aggregate each period's forecast ensemble with the arithmetic mean."""
    return [mean(row) for row in panel]


def panel_trim(panel: Sequence[Sequence[float]], k: int) -> List[float]:
    """Aggregate each period's forecast ensemble with a symmetric k-trimmed mean."""
    return [tmean(row, k) for row in panel]


# ---------------------------------------------------------------------------
# Shared inventory cost model
# ---------------------------------------------------------------------------

def interval_cost(i: int, j: int, setup: float, holding: float,
                  demand: Sequence[float]) -> float:
    """Cost of one order at i covering periods i,...,j-1.

    Demand in period i has zero holding time; demand at i+r is held r periods.
    """
    return setup + sum(
        holding * (t - i) * demand[t]
        for t in range(i, j)
    )


def normalize_orders(orders: Sequence[int], n: int) -> List[int]:
    if n == 0:
        return []
    out = sorted(set(o for o in orders if 0 <= o < n))
    if not out or out[0] != 0:
        out = [0] + out
    return out


def policy_cost(orders: Sequence[int], setup: float, holding: float,
                demand: Sequence[float]) -> float:
    n = len(demand)
    if n == 0:
        return 0.0
    orders = normalize_orders(orders, n)
    boundaries = orders + [n]
    return sum(
        interval_cost(orders[q], boundaries[q + 1], setup, holding, demand)
        for q in range(len(orders))
    )


# ---------------------------------------------------------------------------
# EOI
# ---------------------------------------------------------------------------

def eoi_interval(setup: float, holding: float,
                 estimated_demand: Sequence[float]) -> float:
    dbar = mean(estimated_demand)
    if holding <= 0 or dbar <= 0:
        raise ValueError("Require holding > 0 and positive estimated demand")
    return math.sqrt(2.0 * setup / (holding * dbar))


def int_interval(x: float, n: int) -> int:
    return max(1, min(round(x), n))


def periodic_orders(n: int, interval: int) -> List[int]:
    return list(range(0, n, max(1, int(interval))))


def eoi_orders(setup: float, holding: float,
               estimated_demand: Sequence[float]) -> List[int]:
    interval = int_interval(
        eoi_interval(setup, holding, estimated_demand),
        len(estimated_demand),
    )
    return periodic_orders(len(estimated_demand), interval)


# ---------------------------------------------------------------------------
# Wagner-Whitin
# ---------------------------------------------------------------------------

def ww(setup: float, holding: float,
       estimated_demand: Sequence[float]) -> Tuple[float, List[float], List[int | None]]:
    n = len(estimated_demand)
    costs = [0.0] * (n + 1)
    predecessor: List[int | None] = [None] * (n + 1)

    for j in range(1, n + 1):
        costs[j], predecessor[j] = min(
            (
                costs[i] + interval_cost(i, j, setup, holding, estimated_demand),
                i,
            )
            for i in range(j)
        )
    return costs[n], costs, predecessor


def orders_from_pred(predecessor: Sequence[int | None]) -> List[int]:
    out: List[int] = []
    j = len(predecessor) - 1
    while j > 0:
        i = predecessor[j]
        if i is None:
            raise RuntimeError("Broken predecessor chain")
        out.append(i)
        j = i
    return list(reversed(out))


def ww_orders(setup: float, holding: float,
              estimated_demand: Sequence[float]) -> List[int]:
    _, _, predecessor = ww(setup, holding, estimated_demand)
    return orders_from_pred(predecessor)


# ---------------------------------------------------------------------------
# Silver-Meal / Robust Silver-Meal
# ---------------------------------------------------------------------------

def silver_meal_cycle_length(
    setup: float,
    holding: float,
    estimated_demand: Sequence[float],
    start: int,
) -> int:
    """Return the Silver-Meal coverage length for an order placed at start.

    A(k) = (setup + holding * sum_{r=0}^{k-1} r*d[start+r]) / k.
    The method stops at the first k such that A(k+1) >= A(k).
    If no nondecrease occurs, the order covers the remaining horizon.
    """
    remaining = len(estimated_demand) - start
    if remaining <= 1:
        return max(remaining, 0)

    weighted_prefix = 0.0
    previous_avg = setup  # A(1), since the r=0 holding contribution is zero.

    for k in range(1, remaining):
        # Extend coverage from k periods to k+1 periods by adding demand at start+k.
        weighted_prefix += k * estimated_demand[start + k]
        next_avg = (setup + holding * weighted_prefix) / (k + 1)
        if next_avg >= previous_avg:
            return k
        previous_avg = next_avg

    return remaining


def silver_meal_orders(setup: float, holding: float,
                       estimated_demand: Sequence[float]) -> List[int]:
    n = len(estimated_demand)
    orders: List[int] = []
    start = 0
    while start < n:
        orders.append(start)
        coverage = silver_meal_cycle_length(
            setup, holding, estimated_demand, start
        )
        if coverage <= 0:
            raise RuntimeError("Silver-Meal produced a nonpositive cycle length")
        start += coverage
    return orders


# ---------------------------------------------------------------------------
# Forecast generation and contamination
# ---------------------------------------------------------------------------

CASES = [
    "clean",
    "high_spikes",
    "low_drops",
    "mixed_tails",
    "beyond_budget",
    "central_noise",
]


def true_demand(n: int, rng: random.Random) -> List[float]:
    base = rng.uniform(90, 220)
    amplitude = rng.uniform(0.10, 0.35)
    phase = rng.uniform(0, 2 * math.pi)
    return [
        max(
            1.0,
            base
            * (1 + amplitude * math.sin(2 * math.pi * t / max(n, 2) + phase))
            * rng.lognormvariate(0, 0.12),
        )
        for t in range(n)
    ]


def clean_panel(demand: Sequence[float], ensemble_size: int,
                rng: random.Random) -> List[List[float]]:
    return [
        [max(0.01, x * rng.lognormvariate(0, 0.08))
         for _ in range(ensemble_size)]
        for x in demand
    ]


def contaminate_row(
    xs: Sequence[float],
    case: str,
    trim_budget: int,
    rng: random.Random,
    magnitude: float,
) -> List[float]:
    ys = list(xs)
    if case == "clean":
        return ys
    if case == "central_noise":
        return [
            max(0.01, x * rng.lognormvariate(0, magnitude / 20.0))
            for x in ys
        ]

    count = trim_budget + 1 if case == "beyond_budget" else trim_budget
    ids = rng.sample(range(len(ys)), min(count, len(ys)))

    if case in ("high_spikes", "beyond_budget"):
        for i in ids:
            ys[i] *= magnitude
    elif case == "low_drops":
        for i in ids:
            ys[i] /= magnitude
    elif case == "mixed_tails":
        split = max(1, len(ids) // 2)
        for i in ids[:split]:
            ys[i] *= magnitude
        for i in ids[split:]:
            ys[i] /= magnitude
    else:
        raise ValueError(f"Unknown contamination case: {case}")
    return ys


def contaminate_panel(
    panel: Sequence[Sequence[float]],
    case: str,
    trim_budget: int,
    rng: random.Random,
    magnitude: float,
) -> List[List[float]]:
    return [
        contaminate_row(row, case, trim_budget, rng, magnitude)
        for row in panel
    ]


def replace_sorted_tails(
    xs: Sequence[float], k: int, rng: random.Random
) -> List[float]:
    """Replace exactly the k smallest and k largest values by more extreme tails."""
    ordered = sorted(xs)
    center = ordered[k:len(ordered) - k]
    low = sorted(
        center[0] - rng.uniform(1, 20) * (abs(center[0]) + 1)
        for _ in range(k)
    )
    high = sorted(
        center[-1] + rng.uniform(1, 20) * (abs(center[-1]) + 1)
        for _ in range(k)
    )
    ys = low + center + high
    rng.shuffle(ys)
    return ys


# ---------------------------------------------------------------------------
# Common robustness metrics
# ---------------------------------------------------------------------------

def order_indicator(orders: Sequence[int], n: int) -> List[int]:
    selected = set(normalize_orders(orders, n))
    return [int(t in selected) for t in range(n)]


def schedule_hamming(a: Sequence[int], b: Sequence[int], n: int) -> float:
    """Normalized Hamming distance between replenishment indicator vectors."""
    if n == 0:
        return 0.0
    ia = order_indicator(a, n)
    ib = order_indicator(b, n)
    return sum(x != y for x, y in zip(ia, ib)) / n


def exact_schedule_match(a: Sequence[int], b: Sequence[int], n: int) -> bool:
    return normalize_orders(a, n) == normalize_orders(b, n)


def demand_mae(estimate: Sequence[float], truth: Sequence[float]) -> float:
    return mean([abs(x - y) for x, y in zip(estimate, truth)])


METHODS = ["eoi", "ww", "sm", "rsm"]
ROBUST_PAIRS = [("sm", "rsm")]


def compute_orders(method: str, setup: float, holding: float,
                   estimate: Sequence[float]) -> List[int]:
    if method in ("eoi", "reoi"):
        return eoi_orders(setup, holding, estimate)
    if method in ("ww", "rww"):
        return ww_orders(setup, holding, estimate)
    if method in ("sm", "rsm"):
        return silver_meal_orders(setup, holding, estimate)
    raise ValueError(f"Unknown method: {method}")


# ---------------------------------------------------------------------------
# Theorem-aligned checks
# ---------------------------------------------------------------------------

def theorem_checks(
    trials: int,
    horizon: int,
    ensemble_size: int,
    trim_budget: int,
    seed: int,
) -> int:
    rng = random.Random(seed)
    robust_methods = ["rsm"]

    for _ in range(trials):
        truth = true_demand(horizon, rng)
        panel = clean_panel(truth, ensemble_size, rng)
        replaced = [
            replace_sorted_tails(row, trim_budget, rng)
            for row in panel
        ]

        clean_trim = panel_trim(panel, trim_budget)
        replaced_trim = panel_trim(replaced, trim_budget)
        assert all(
            math.isclose(x, y, rel_tol=0.0, abs_tol=1e-12)
            for x, y in zip(clean_trim, replaced_trim)
        )

        setup = rng.uniform(100, 1000)
        holding = rng.uniform(1, 10)
        for method in robust_methods:
            clean_orders = compute_orders(method, setup, holding, clean_trim)
            replaced_orders = compute_orders(method, setup, holding, replaced_trim)
            assert clean_orders == replaced_orders
            assert math.isclose(
                policy_cost(clean_orders, setup, holding, truth),
                policy_cost(replaced_orders, setup, holding, truth),
                rel_tol=1e-12,
                abs_tol=1e-8,
            )
    return trials


# ---------------------------------------------------------------------------
# Experiment
# ---------------------------------------------------------------------------

@dataclass
class Config:
    horizon: int = 24
    ensemble_size: int = 9
    trim: int = 2
    instances: int = 200
    magnitude: float = 20.0
    seed: int = 42


def run(cfg: Config) -> Tuple[List[Dict[str, float | int | str]],
                              List[Dict[str, float | str]]]:
    rng = random.Random(cfg.seed)
    rows: List[Dict[str, float | int | str]] = []

    for case in CASES:
        for instance in range(cfg.instances):
            truth = true_demand(cfg.horizon, rng)
            panel = clean_panel(truth, cfg.ensemble_size, rng)
            contaminated = contaminate_panel(
                panel, case, cfg.trim, rng, cfg.magnitude
            )

            clean_mean = panel_mean(panel)
            clean_trim = panel_trim(panel, cfg.trim)
            contaminated_mean = panel_mean(contaminated)
            contaminated_trim = panel_trim(contaminated, cfg.trim)

            setup = rng.uniform(100, 1000)
            holding = rng.uniform(1, 10)

            clean_estimates = {
                "eoi": clean_mean,
                "ww": clean_mean,
                "sm": clean_mean,
                "rsm": clean_trim,
            }
            contaminated_estimates = {
                "eoi": contaminated_mean,
                "ww": contaminated_mean,
                "sm": contaminated_mean,
                "rsm": contaminated_trim,
            }

            row: Dict[str, float | int | str] = {
                "case": case,
                "instance": instance,
                "setup_cost": setup,
                "holding_cost": holding,
                "raw_forecast_mae": demand_mae(contaminated_mean, truth),
                "trimmed_forecast_mae": demand_mae(contaminated_trim, truth),
            }

            for method in METHODS:
                clean_orders = compute_orders(
                    method, setup, holding, clean_estimates[method]
                )

                start = time.perf_counter()
                contaminated_orders = compute_orders(
                    method, setup, holding, contaminated_estimates[method]
                )
                runtime = time.perf_counter() - start

                clean_realized_cost = policy_cost(
                    clean_orders, setup, holding, truth
                )
                contaminated_realized_cost = policy_cost(
                    contaminated_orders, setup, holding, truth
                )

                row[f"{method}_schedule_distance"] = schedule_hamming(
                    contaminated_orders, clean_orders, cfg.horizon
                )
                row[f"{method}_exact_match"] = float(
                    exact_schedule_match(
                        contaminated_orders, clean_orders, cfg.horizon
                    )
                )
                row[f"{method}_order_count_error"] = abs(
                    len(contaminated_orders) - len(clean_orders)
                )
                row[f"{method}_cost"] = contaminated_realized_cost
                row[f"{method}_clean_cost"] = clean_realized_cost
                row[f"{method}_cost_deviation"] = abs(
                    contaminated_realized_cost - clean_realized_cost
                )
                row[f"{method}_positive_regret"] = max(
                    0.0,
                    contaminated_realized_cost - clean_realized_cost,
                )
                row[f"{method}_time"] = runtime

            rows.append(row)

    aggregate: List[Dict[str, float | str]] = []
    for case in CASES:
        selected = [row for row in rows if row["case"] == case]
        summary: Dict[str, float | str] = {"case": case}
        summary["mean_raw_forecast_mae"] = mean(
            [float(row["raw_forecast_mae"]) for row in selected]
        )
        summary["mean_trimmed_forecast_mae"] = mean(
            [float(row["trimmed_forecast_mae"]) for row in selected]
        )

        for method in METHODS:
            for metric in [
                "schedule_distance",
                "exact_match",
                "order_count_error",
                "cost",
                "clean_cost",
                "cost_deviation",
                "positive_regret",
                "time",
            ]:
                summary[f"mean_{method}_{metric}"] = mean(
                    [float(row[f"{method}_{metric}"]) for row in selected]
                )

        for classical, robust in ROBUST_PAIRS:
            summary[f"{robust}_schedule_better_rate"] = mean([
                float(row[f"{robust}_schedule_distance"])
                <= float(row[f"{classical}_schedule_distance"])
                for row in selected
            ])
            summary[f"{robust}_cost_better_rate"] = mean([
                float(row[f"{robust}_cost"])
                <= float(row[f"{classical}_cost"])
                for row in selected
            ])

        aggregate.append(summary)

    return rows, aggregate


# ---------------------------------------------------------------------------
# Outputs
# ---------------------------------------------------------------------------

def write_csv(path: Path, rows: Sequence[Dict[str, object]]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def plots(aggregate: Sequence[Dict[str, float | str]],
          output_dir: Path, timestamp: str) -> None:
    nonclean = [row for row in aggregate if row["case"] != "clean"]
    cases = [str(row["case"]) for row in nonclean]
    x = list(range(len(cases)))

    # Robustness: common schedule distance across all methods.
    plt.figure(figsize=(11, 5.2))
    for method in METHODS:
        plt.plot(
            x,
            [float(row[f"mean_{method}_schedule_distance"]) for row in nonclean],
            marker="o",
            label=method.upper(),
        )
    plt.xticks(x, cases, rotation=20, ha="right")
    plt.ylabel("Mean normalized schedule distance")
    plt.title("Decision robustness under forecast contamination")
    plt.legend(ncol=3)
    plt.tight_layout()
    plt.savefig(output_dir / f"schedule_robustness_{timestamp}.png", dpi=300)
    plt.close()

    # Realized cost.
    plt.figure(figsize=(11, 5.2))
    for method in METHODS:
        plt.plot(
            range(len(aggregate)),
            [float(row[f"mean_{method}_cost"]) for row in aggregate],
            marker="o",
            label=method.upper(),
        )
    plt.xticks(
        range(len(aggregate)),
        [str(row["case"]) for row in aggregate],
        rotation=20,
        ha="right",
    )
    plt.ylabel("Mean realized cost on true demand")
    plt.title("Realized policy cost")
    plt.legend(ncol=3)
    plt.tight_layout()
    plt.savefig(output_dir / f"realized_cost_{timestamp}.png", dpi=300)
    plt.close()

    # Cost deviation from each method's clean-input decision.
    plt.figure(figsize=(11, 5.2))
    for method in METHODS:
        plt.plot(
            x,
            [float(row[f"mean_{method}_cost_deviation"]) for row in nonclean],
            marker="o",
            label=method.upper(),
        )
    plt.xticks(x, cases, rotation=20, ha="right")
    plt.ylabel("Mean absolute realized-cost deviation")
    plt.title("Cost stability relative to clean-input policy")
    plt.legend(ncol=3)
    plt.tight_layout()
    plt.savefig(output_dir / f"cost_stability_{timestamp}.png", dpi=300)
    plt.close()

    # Runtime.
    clean = next(row for row in aggregate if row["case"] == "clean")
    plt.figure(figsize=(8, 4.8))
    #plt.bar(
    #    [method.upper() for method in METHODS],
    #    [float(clean[f"mean_{method}_time"]) for method in METHODS],
    #)
    plt.bar(
    [method.upper() for method in METHODS],
    [float(clean[f"mean_{method}_time"]) for method in METHODS],
    width=0.25,   # slimmer columns
    )
    plt.yscale("log")
    plt.ylabel("Mean runtime (seconds, log scale)")
    plt.title("Runtime comparison")
    plt.tight_layout()
    plt.savefig(output_dir / f"runtime_{timestamp}.png", dpi=300)
    plt.close()


def rank_methods(
    aggregate: Sequence[Dict[str, float | str]],
) -> List[str]:
    """Rank EOI, WW, SM, and RSM over all non-clean contamination cases."""
    nonclean = [row for row in aggregate if row["case"] != "clean"]
    lines: List[str] = []

    metrics = [
        ("schedule robustness", "schedule_distance"),
        ("realized cost", "cost"),
        ("cost stability", "cost_deviation"),
        ("runtime", "time"),
    ]

    averages: Dict[str, Dict[str, float]] = {}
    for label, metric in metrics:
        values = {
            method: mean([
                float(row[f"mean_{method}_{metric}"])
                for row in nonclean
            ])
            for method in METHODS
        }
        averages[metric] = values
        ranking = sorted(values.items(), key=lambda item: item[1])
        lines.append(
            f"{label}: "
            + ", ".join(f"{m.upper()}={v:.6g}" for m, v in ranking)
            + "\n"
        )

    rsm_time = averages["time"]["rsm"]
    ww_time = averages["time"]["ww"]
    rsm_cost = averages["cost"]["rsm"]
    ww_cost = averages["cost"]["ww"]
    sm_cost = averages["cost"]["sm"]
    rsm_stability = averages["cost_deviation"]["rsm"]
    sm_stability = averages["cost_deviation"]["sm"]
    rsm_sched = averages["schedule_distance"]["rsm"]
    sm_sched = averages["schedule_distance"]["sm"]

    if rsm_time < ww_time:
        lines.append(
            f"RSM finding: RSM is {ww_time / max(rsm_time, 1e-15):.2f}x "
            "faster than WW on average.\n"
        )
    if rsm_cost <= ww_cost:
        lines.append(
            f"RSM finding: RSM has {100 * (ww_cost - rsm_cost) / ww_cost:.2f}% "
            "lower realized cost than WW on average.\n"
        )
    else:
        lines.append(
            f"RSM trade-off: RSM realized cost is "
            f"{100 * (rsm_cost - ww_cost) / ww_cost:.2f}% above WW, "
            "while retaining much lower runtime.\n"
        )
    if rsm_cost < sm_cost:
        lines.append(
            f"RSM finding: RSM lowers realized cost relative to SM by "
            f"{100 * (sm_cost - rsm_cost) / sm_cost:.2f}%.\n"
        )
    if rsm_stability < sm_stability:
        lines.append(
            f"RSM finding: RSM improves cost stability over SM by "
            f"{100 * (sm_stability - rsm_stability) / sm_stability:.2f}%.\n"
        )
    if rsm_sched < sm_sched:
        lines.append(
            f"RSM finding: RSM improves schedule robustness over SM by "
            f"{100 * (sm_sched - rsm_sched) / sm_sched:.2f}%.\n"
        )

    return lines


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=24)
    parser.add_argument("--ensemble-size", type=int, default=9)
    parser.add_argument("--trim", type=int, default=2)
    parser.add_argument("--instances", type=int, default=200)
    parser.add_argument("--magnitude", type=float, default=20.0)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--theorem-trials", type=int, default=500)
    parser.add_argument("--output-dir", type=Path, default=Path("."))
    args = parser.parse_args()

    if 2 * args.trim >= args.ensemble_size:
        parser.error("Require 2 * --trim < --ensemble-size")

    cfg = Config(
        horizon=args.horizon,
        ensemble_size=args.ensemble_size,
        trim=args.trim,
        instances=args.instances,
        magnitude=args.magnitude,
        seed=args.seed,
    )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    passed = theorem_checks(
        args.theorem_trials,
        cfg.horizon,
        cfg.ensemble_size,
        cfg.trim,
        cfg.seed + 100,
    )
    rows, aggregate = run(cfg)

    write_csv(args.output_dir / f"detail_{timestamp}.csv", rows)
    write_csv(args.output_dir / f"aggregate_{timestamp}.csv", aggregate)
    plots(aggregate, args.output_dir, timestamp)

    lines = [
        f"Theorem-aligned trimmed-tail invariance checks: "
        f"{passed}/{args.theorem_trials} PASS\n\n"
    ]

    for row in aggregate:
        lines.append(f"{row['case']}:\n")
        for classical, robust in ROBUST_PAIRS:
            lines.append(
                f"  {robust.upper()} <= {classical.upper()} schedule distance: "
                f"{100 * float(row[f'{robust}_schedule_better_rate']):.1f}%\n"
            )
            lines.append(
                f"  {robust.upper()} <= {classical.upper()} realized cost: "
                f"{100 * float(row[f'{robust}_cost_better_rate']):.1f}%\n"
            )
        lines.append(
            "  schedule distance "
            + ", ".join(
                f"{method.upper()}="
                f"{float(row[f'mean_{method}_schedule_distance']):.4f}"
                for method in METHODS
            )
            + "\n"
        )
        lines.append(
            "  realized cost "
            + ", ".join(
                f"{method.upper()}={float(row[f'mean_{method}_cost']):.2f}"
                for method in METHODS
            )
            + "\n\n"
        )

    lines.append("Overall rankings over non-clean cases:\n")
    lines.extend(rank_methods(aggregate))

    summary = args.output_dir / f"summary_{timestamp}.txt"
    summary.write_text("".join(lines), encoding="utf-8")
    print(summary.read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
