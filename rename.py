import os
files = [os.path.join(dp, f) for dp, dn, fn in os.walk(os.path.expanduser(".")) for f in fn]

i=0
for file in files:
    if file.endswith("_auto.lean"):
        newname = file[:-10] + ".lean"
        os.rename(file, newname)