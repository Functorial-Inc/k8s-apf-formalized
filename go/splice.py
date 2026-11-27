# /// script
# requires-python = ">=3.9"
# ///
"""Replace one top-level Go function in a file with text read from stdin.

Usage: splice.py FILE 'func (qs *queueSet) removeQueueIfEmptyLocked('
The function is the span from the line starting with the given prefix to the
first following line that is exactly '}'. Fails unless there is exactly one.
"""
import sys

path, prefix = sys.argv[1], sys.argv[2]
new = sys.stdin.read()
lines = open(path).read().split("\n")
starts = [i for i, l in enumerate(lines) if l.startswith(prefix)]
if len(starts) != 1:
    sys.exit(f"expected exactly one function starting with {prefix!r}, found {len(starts)}")
a = starts[0]
b = next(i for i in range(a, len(lines)) if lines[i] == "}")
out = lines[:a] + new.rstrip("\n").split("\n") + lines[b + 1:]
open(path, "w").write("\n".join(out))
