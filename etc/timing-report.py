#!/usr/bin/env python3

from __future__ import print_function

import sqlite3
import pandas as pd


def read_db(fname):
    conn = sqlite3.connect(fname)
    conn.row_factory = sqlite3.Row
    qed_timings = []
    for row in conn.execute("SELECT fname, ident, time FROM qed_timings"):
        qed_timings.append((row["fname"], row["ident"], row["time"]))

    file_timings = []
    for row in conn.execute("""SELECT fname, time FROM file_timings"""):
        file_timings.append((row["fname"], row["time"]))
    conn.close()

    qed_df = pd.DataFrame(qed_timings, columns=["fname", "ident", "time"])
    qed_sum = qed_df.groupby("fname").sum()
    raw_file_df = pd.DataFrame(file_timings, columns=["fname", "time"])
    file_df = raw_file_df.join(qed_sum, rsuffix="_qed", on="fname")
    file_df.rename(
        mapper={"time_qed": "qed_time"}, axis="columns", inplace=True
    )
    file_df.fillna(value={"qed_time": 0.0}, inplace=True)
    return qed_df, file_df


def filter_df(df, col=None, pat=None):
    return df[df[col].str.contains(pat)]


if __name__ == "__main__":
    import argparse
    import os.path
    import sys

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--max-files",
        type=int,
        default=10,
        help="number of slow files to show",
    )
    parser.add_argument(
        "--max-qeds",
        type=int,
        default=0,
        help="number of slow QED proofs to show",
    )
    parser.add_argument(
        "--db", help="sqlite database of timing info", default=".timing.sqlite3"
    )
    parser.add_argument("--filter", help="filter file names", default=None)

    args = parser.parse_args()

    if not os.path.exists(args.db):
        print("database file {} not found".format(args.db), file=sys.stderr)
        sys.exit(1)
    qed_df, file_df = read_db(args.db)
    pd.set_option("display.max_rows", 100)
    pd.set_option("display.max_columns", 10)
    pd.set_option("display.width", 300)
    if args.filter is not None:
        file_df = filter_df(file_df, col="fname", pat=args.filter)
    total_s = file_df["time"].sum()
    print("{:12s} {:>6.1f}".format("total", total_s))
    print(
        "{:12s} {:>6.1f}".format(
            "  Iris",
            filter_df(file_df, col="fname", pat="^external/iris")["time"].sum(),
        )
    )
    print(
        "{:12s} {:>6.1f}".format(
            "  stdpp",
            filter_df(file_df, col="fname", pat="^external/stdpp")[
                "time"
            ].sum(),
        )
    )
    qed_s = file_df["qed_time"].sum()
    print(
        "{:12s} {:>6.1f} ({:0.0f}%)".format(
            "Qed total", qed_s, qed_s / total_s * 100
        )
    )

    if args.max_files > 0 or args.max_qeds > 0:
        print()
        print("slow files:")
        print(file_df.nlargest(args.max_files, "time").to_string(index=False))

        if args.max_qeds > 0 and len(qed_df) > 0:
            print()
            print("slow QEDs:")
            print(qed_df.nlargest(args.max_qeds, "time").to_string(index=False))
