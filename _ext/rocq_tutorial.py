from pathlib import Path


def hide_proofs(app):
    srcdir = Path(app.srcdir)

    files = srcdir.glob("*.v")

    rocqdir = srcdir / "rocq"
    rocqdir.mkdir(exist_ok=True)

    start_marker = "Proof. (** HIDE *)\n"
    end_marker = "Qed.\n"

    replacement = "Proof.\nAdmitted.\n"

    for src in files:
        clear_text = src.read_text()

        dst = rocqdir / src.name

        with dst.open("w") as f:
            while True:
                i = clear_text.find(start_marker)

                if i == -1:
                    break

                f.write(clear_text[:i])
                f.write(replacement)

                clear_text = clear_text[i + len(start_marker) :]

                i = clear_text.find(end_marker)

                assert i != -1

                clear_text = clear_text[i + len(end_marker) :]


def setup(app):
    app.connect("builder-inited", hide_proofs)
