"""Run the positive-path census, one independent intersection count per process."""
import argparse
import concurrent.futures
import csv
import os
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, help="compiled certify_lower executable")
    parser.add_argument("distance", type=int, choices=[4, 5, 6])
    parser.add_argument("last", type=int, help="last intersection count, inclusive")
    parser.add_argument("output", type=Path, help="per-size transcripts and combined CSV")
    parser.add_argument("--first", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--verify", action="store_true", help="compare every result to the published CSV")
    args = parser.parse_args()
    if not 1 <= args.first <= args.last or args.jobs < 1:
        parser.error("expected a positive size range and worker count")
    args.output.mkdir(parents=True, exist_ok=True)
    binary = str(args.binary.resolve())

    def run_size(n):
        proc = subprocess.run([binary, str(args.distance), str(n), str(n), "all"],
                              capture_output=True, text=True, check=True)
        (args.output / f"{n:03}.txt").write_text(proc.stdout, encoding="utf-8")
        fields = proc.stdout.splitlines()[-1].split()
        if fields[:3] != ["ROW", str(args.distance), str(n)]:
            raise RuntimeError(f"missing summary for size {n}")
        row = dict(zip(fields[3::2], map(int, fields[4::2])))
        if row["complete"] != 1 or row["connected"] != row["rejected"] + row["survivors"]:
            raise RuntimeError(f"incomplete accounting for size {n}")
        if row["survivors"] or n % 10 == 0 or n == args.last:
            print(" ".join(fields), flush=True)
        return {"distance": args.distance, "crossings": n, **row}

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(run_size, range(args.first, args.last+1)))
    with (args.output / "census.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print("Unresolved diagrams:", sum(r["survivors"] for r in rows), flush=True)
    if args.verify:
        release = Path(__file__).with_name("census.csv")
        with release.open(encoding="utf-8") as stream:
            expected = {int(r["crossings"]): {key:int(value) for key,value in r.items()}
                        for r in csv.DictReader(stream) if int(r["distance"]) == args.distance}
        for row in rows:
            if expected.get(row["crossings"]) != row:
                raise RuntimeError(f"published census differs or has no entry at {row['crossings']} crossings")
        print(f"All {len(rows)} rows match {release.name}.", flush=True)


if __name__ == "__main__":
    main()
