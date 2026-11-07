import io
from pathlib import Path
import tarfile

def hide_proof(text, sink):
    start_marker = "Proof. (** HIDE *)\n"
    end_marker = "Qed.\n"

    replacement = "Proof.\nAdmitted.\n"

    while True:
        i = clear_text.find(start_marker)

        if i == -1:
            break

        sink.write(clear_text[:i])
        sink.write(replacement)

        clear_text = clear_text[i + len(start_marker) :]

        i = clear_text.find(end_marker)

        assert i != -1

        clear_text = clear_text[i + len(end_marker) :]

def process_dir(srcdir, dir):
    tarpath = srcdir / dir.with_suffix(".tgz")
    tarpath.unlink(missing_ok=True)

    archive = tarfile.open(tarpath, "x:gz")

    rocqproject_path = dir / "_RocqProject"
    expected_contents = "-Q . " + dir.name + "\n"
    assert rocqproject_path.read_text() == expected_contents

    well_known_files = [rocqproject_path, dir / "Makefile", dir / "Makefile.conf"]

    for file in well_known_files:
        archive.add(file)

    # We cannot use archive.add for the Rocq files because we need to perform
    # proof hiding on the contents first.

    rocq_files = dir.glob("*.v")

    for file in rocq_files:
        info = archive.gettarinfo(file)

        with file.open() as f:
            text_with_proofs_hidden = hide_proof (f.read_text())
            file_object = io.BytesIO(text_with_proofs_hidden)
            archive.addfile(info, file_object)

    archive.close()

def loop_over_dirs(app):
    srcdir = Path(app.srcdir)
    
    for dir in app.config.rocq_tutorial_dirs:
        process_dir(srcdir, srcdir / dir)

def hide_proof(text, sink):
    start_marker = "Proof. (** HIDE *)\n"
    end_marker = "Qed.\n"

    replacement = "Proof.\nAdmitted.\n"

    clear_text = text

    while True:
        i = clear_text.find(start_marker)

        if i == -1:
            break

        sink.write(clear_text[:i])
        sink.write(replacement)

        clear_text = clear_text[i + len(start_marker) :]

        i = clear_text.find(end_marker)

        assert i != -1

        clear_text = clear_text[i + len(end_marker) :]


def process_dir(srcdir, dir):
    tarpath = srcdir / dir.with_suffix(".tgz")
    tarpath.unlink(missing_ok=True)

    archive = tarfile.open(tarpath, "x:gz")

    rocqproject_path = dir / "_RocqProject"
    expected_contents = "-Q . " + dir.name + "\n"
    assert rocqproject_path.read_text() == expected_contents

    well_known_files = [rocqproject_path, dir / "Makefile", dir / "Makefile.conf"]

    for file in well_known_files:
        archive.add(file, arcname=file.relative_to(srcdir))

    # We cannot use archive.add for the Rocq files because we need to perform
    # proof hiding on the contents first.

    rocq_files = dir.glob("*.v")

    for file in rocq_files:
        info = archive.gettarinfo(file)

        file_text = io.StringIO()
        hide_proof(file.read_text(), file_text)

        file_object = io.BytesIO(file_text.getvalue().encode())

        info.size = len(file_object.getbuffer())
        info.name = file.relative_to(srcdir).as_posix()

        archive.addfile(info, file_object)

    archive.close()


def loop_over_dirs(app):
    srcdir = Path(app.srcdir)

    for dir in app.config.rocq_tutorial_dirs:
        process_dir(srcdir, srcdir / dir)


def setup(app):
    app.add_config_value("rocq_tutorial_dirs", [], "html")

    app.connect("builder-inited", loop_over_dirs)
