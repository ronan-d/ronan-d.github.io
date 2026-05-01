import datetime
from enum import Enum, auto
import locale
from pathlib import Path
import subprocess

index_header = """
All articles on this site
=========================

.. toctree::
   :maxdepth: 1

"""


class Event(Enum):
    FIRST_PUBLICATION = auto()
    LATEST_UPDATE = auto()


def git_args(event):
    match event:
        case Event.FIRST_PUBLICATION:
            return ["--diff-filter=A"]
        case Event.LATEST_UPDATE:
            return []


def insert_after_title(page, line):
    lines = page.splitlines()

    lines.insert(2, line)
    lines.insert(2, "")

    return "\n".join(lines) + "\n"


def get_ts(path, event):
    cmd = (
        ["git", "log"]
        + git_args(event)
        + [
            "-n",
            "1",
            "--format=format:%at",
            path,
        ]
    )

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=True,
    )
    return int(result.stdout.strip())


def ts2str(ts):
    saved_locale = locale.getlocale(locale.LC_TIME)
    locale.setlocale(locale.LC_TIME, "en_US.utf8")
    d = datetime.date.fromtimestamp(ts)
    ret = d.strftime("%B %-d %-Y")
    locale.setlocale(locale.LC_TIME, saved_locale)
    return ret


def get_str(path, event):
    ts = get_ts(path, event)
    return ts2str(ts)


def get_first_publication_date(path):
    return get_str(path, Event.FIRST_PUBLICATION)


def get_latest_update_date(path):
    return get_str(path, Event.LATEST_UPDATE)


def get_first_publication_timestamp(path):
    return get_ts(path, Event.FIRST_PUBLICATION)


def generate_index(app):
    srcdir = Path(app.srcdir)
    outfile = srcdir / "index.rst"

    # Find all .rst files except index itself
    pages = sorted(
        (p.relative_to(srcdir) for p in srcdir.rglob("*.rst") if p.name != "index.rst"),
        key=get_first_publication_timestamp,
    )

    with outfile.open("w") as f:

        f.write(index_header)

        for page in pages:
            # toctree entries omit the extension
            entry = page.with_suffix("")
            f.write(f"   {entry}\n")


def add_date_line(app, docname, content):
    if docname == "index":
        return

    path = f"{docname}.rst"

    f = get_first_publication_date(path)
    l = get_latest_update_date(path)

    phrase = f"First published {f}; Last updated {l}" if f != l else f

    date_line = f"*{phrase}.*"

    content[0] = insert_after_title(content[0], date_line)


def setup(app):
    app.connect("builder-inited", generate_index)
    app.connect("source-read", add_date_line)

    return {
        "version": "0.1",
        "parallel_read_safe": True,
    }
