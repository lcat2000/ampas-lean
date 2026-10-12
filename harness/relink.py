#!/usr/bin/env python3
"""Link a lake-built Lean executable on this machine.

The conda-forge Lean records its build-time library paths as unresolvable
placeholders (/home/conda/.../host_env_placehold.../lib/libgmp.so) and asks
for -luv, which is not an available linker name here. lake's own link step
therefore fails for every executable. This takes lake's response file,
substitutes the system shared libraries for the placeholder ones, drops the
placeholder -L/-rpath entries, and links with the system gcc.
"""
import shlex, subprocess, sys, os
rsp, out, sysroot = sys.argv[1], sys.argv[2], sys.argv[3]
SUB = {"libgmp.so": "/lib/x86_64-linux-gnu/libgmp.so.10",
       "libssl.so": "/lib/x86_64-linux-gnu/libssl.so.3",
       "libcrypto.so": "/lib/x86_64-linux-gnu/libcrypto.so.3"}
args = []
for t in shlex.split(open(rsp).read()):
    if "/home/conda/" in t:
        base = os.path.basename(t)
        if base in SUB:
            args.append(SUB[base])
        continue                      # drop placeholder -L / -rpath / -rpath-link
    if t == "-luv":
        args.append("/lib/x86_64-linux-gnu/libuv.so.1"); continue
    args.append(t)
argfile = rsp + ".fixed"
open(argfile, "w").write("\n".join(args))
cmd = ["gcc", "-o", out, f"@{argfile}", f"-Wl,-rpath,{sysroot}/lib/lean"]
r = subprocess.run(cmd, capture_output=True, text=True)
print(r.stdout[-2000:], r.stderr[-2000:])
sys.exit(r.returncode)
