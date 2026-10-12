"""CLI: python3 -m kernel <export.txt> [--json out.json] [--verify NAME...]"""
import argparse, json, sys, time
from .parse import parse_export
from .check import check_env, Checker, TypeError_


def main(argv):
    ap = argparse.ArgumentParser(prog="kernel")
    ap.add_argument("export")
    ap.add_argument("--json")
    ap.add_argument("--verify", nargs="*", default=[],
                    help="constants that must be present and well-typed")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    t0 = time.time()
    env = parse_export(args.export)
    t_parse = time.time() - t0
    t0 = time.time()
    def prog(i, n, name):
        if not args.quiet:
            print(f"  [{i}/{n}] {name}", file=sys.stderr)
    res = check_env(env, progress=prog)
    res["seconds"] = round(time.time() - t0, 2)
    res["parse_seconds"] = round(t_parse, 2)
    res["module"] = env.module
    res["roots"] = env.roots
    # a root counts as verified only if it is present AND the whole closure
    # it depends on checked without error
    res["verified"] = {}
    for name in args.verify:
        present = any(k.str == name for k in env.decls)
        res["verified"][name] = present and not res["errors"]
    res["ok"] = not res["errors"] and all(res["verified"].values())
    out = json.dumps(res, indent=2)
    if args.json:
        open(args.json, "w").write(out)
    print(out)
    return 0 if res["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
