#!/usr/bin/env python3
##############################################################################
##                                                                          ##
##                   Verification Condition Generator                       ##
##                                                                          ##
##              Copyright (C) 2023, Florian Schanda                         ##
##                                                                          ##
##  This file is part of PyVCG.                                             ##
##                                                                          ##
##  PyVCG is free software: you can redistribute it and/or modify it        ##
##  under the terms of the GNU General Public License as published by       ##
##  the Free Software Foundation, either version 3 of the License, or       ##
##  (at your option) any later version.                                     ##
##                                                                          ##
##  PyVCG is distributed in the hope that it will be useful, but            ##
##  WITHOUT ANY WARRANTY; without even the implied warranty of              ##
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU        ##
##  General Public License for more details.                                ##
##                                                                          ##
##  You should have received a copy of the GNU General Public License       ##
##  along with PyVCG. If not, see <http://www.gnu.org/licenses/>.           ##
##                                                                          ##
##############################################################################

# Helper script to remove "-dev" from current version; update
# changelog/docs; and commit.

import os

import util.changelog

# Update version.py to remove the -dev (or if given) use a different
# version number.

VERSION_FILE = os.path.join("pyvcg", "version.py")

tmp = ""
with open(VERSION_FILE, "r") as fd:
    for raw_line in fd:
        if raw_line.startswith("VERSION_SUFFIX"):
            raw_line = 'VERSION_SUFFIX = ""\n'
        tmp += raw_line

with open(VERSION_FILE, "w") as fd:
    fd.write(tmp)

from pyvcg.version import PYVCG_VERSION
print(PYVCG_VERSION)

# Update last CHANGELOG entry and documentation to use the new
# version.

util.changelog.set_current_title(PYVCG_VERSION)

# Commit

os.system("git add CHANGELOG.md pyvcg/version.py")
os.system('git commit -m "PyVCG Release %s"' % PYVCG_VERSION)
