#!/usr/bin/env python3
import os, re, subprocess, sys, tempfile

def blockquote(s):
    return "\n".join("> " + line for line in s.rstrip("\n").split("\n"))

def find_error_line():  # 0-based
    print("Running agda")
    compile_output = subprocess.run(["agda", "--safe", "chad-cost.agda"], capture_output=True, cwd="..").stdout.decode("utf-8")
    for line in compile_output.split("\n"):
        if len(line) > 0 and line[0] == "/":
            m = re.search(r":([0-9]+)", line)
            assert m is not None
            print(blockquote(compile_output))
            return int(m[1]) - 1
    return None

def list_with(l, i, x):
    return l[:i] + [x] + l[i+1:]

def link_agdas(srcdir, destdir, **kwargs):
    exclude = kwargs.get("exclude", [])
    for fname in os.listdir(srcdir):
        if fname in exclude: continue
        if "." in fname and fname[fname.rfind("."):] in [".agda", ".agda-lib"]:
            print("Linking '{}' -> '{}'".format(destdir + "/" + fname, srcdir + "/" + fname))
            os.symlink(srcdir + "/" + fname, destdir + "/" + fname)

def main():
    errorlnum = find_error_line()
    if errorlnum is None:
        print("Done, all OK!")
        return

    print("Found agda error at line {}".format(errorlnum + 1))

    with open("../chad-cost.agda") as f: chad_cost_src = f.read().split("\n")
    errorline = chad_cost_src[errorlnum]

    print("Line there:")
    print(blockquote(errorline))

    m = re.search(r"{- LEMMA -} ([^ ]*)", errorline)
    if m is None:
        print("No LEMMA comment found on error line")
        return 1
    lemma_name = m[1]

    print("Using lemma '{}'".format(lemma_name))

    with open("../lemmas.agda") as f: lemmas_src = f.read().split("\n")
    for i, line in enumerate(lemmas_src):
        if line.find(lemma_name) != -1:
            lemma_decl_lnum = i
            print("Lemma found in lemmas.agda at line {}".format(lemma_decl_lnum + 1))
            break
    else:
        print("Lemma not found in lemmas.agda")
        return 1

    tacticstr = re.sub(r"^ *-- *", "", lemmas_src[lemma_decl_lnum - 1])
    print("Tactic string:")
    print(blockquote(tacticstr))

    with tempfile.TemporaryDirectory() as workdir:
        tmpfname = workdir + "/chad-cost.agda"
        print("Writing patched chad-cost.agda to '{}'".format(tmpfname))
        with open(tmpfname, "w") as f:
            f.write("\n".join(re.sub(r"{- LEMMA -}", "? --", line) if i >= errorlnum else line
                              for i, line in enumerate(chad_cost_src)))

        link_agdas(os.getcwd() + "/..", workdir, exclude=["chad-cost.agda"])
        os.mkdir(workdir + "/spec")
        link_agdas(os.getcwd() + "/../spec", workdir + "/spec")

        viafile = workdir + "/ser.context"

        result = subprocess.run(["cabal", "exec", "arith-solver", "--", "-ctx", tmpfname, "0", viafile], capture_output=True)
        if result.returncode != 0:
            print("Getting context failed:")
            print(blockquote(result.stdout.decode("utf-8")))
            print("--")
            print(blockquote(result.stderr.decode("utf-8")))
            return 1
        prove_out = subprocess.check_output(["cabal", "exec", "arith-solver", "--", "-prove", viafile, tacticstr, lemma_name]).decode("utf-8")
        print("Prover output:")
        print(blockquote(prove_out))

    lemma_def = prove_out.split("\n")[0:4]
    lemma_use = prove_out.split("\n")[5]

    print("Replacing lemma in lemmas.agda")
    with open("../lemmas.agda", "w") as f:
        repl_base = lemma_decl_lnum - 1
        f.write("\n".join("  " + lemma_def[i - repl_base]
                            if repl_base <= i < repl_base + 4
                            else line
                          for i, line in enumerate(lemmas_src)))

    print("Replacing lemma use in chad-cost.agda: from")
    print(blockquote(errorline))
    print("to")
    idx = errorline.index("{- LEMMA -} ")
    patched_errorline = errorline[:idx + 12] + lemma_use
    print(blockquote(patched_errorline))

    with open("../chad-cost.agda", "w") as f:
        f.write("\n".join(list_with(chad_cost_src, errorlnum, patched_errorline)))

    print("Done.")

if __name__ == "__main__":
    ret = main()
    if ret is not None:
        sys.exit(ret)
