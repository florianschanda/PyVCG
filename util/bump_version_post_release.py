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

import os

import util.changelog

from pyvcg.version import VERSION_TUPLE

major, minor, release = VERSION_TUPLE
release += 1

# Bump version and update version.py

VERSION_FILE = os.path.join("pyvcg", "version.py")

tmp = ""
with open(VERSION_FILE, "r") as fd:
    for raw_line in fd:
        if raw_line.startswith("VERSION_TUPLE"):
            raw_line = 'VERSION_TUPLE = (%u, %u, %u)\n' % (major,
                                                           minor,
                                                           release)
        elif raw_line.startswith("VERSION_SUFFIX"):
            raw_line = 'VERSION_SUFFIX = "dev"\n'

        tmp += raw_line
with open(VERSION_FILE, "w") as fd:
    fd.write(tmp)

PYVCG_VERSION = "%u.%u.%u-dev" % (major, minor, release)

# Update changelog and docs, adding a new entry

util.changelog.add_new_section(PYVCG_VERSION)

# Assemble commit

os.system("git add pyvcg/version.py CHANGELOG.md")
os.system('git commit -m "Bump version to %s after release"' % PYVCG_VERSION)
