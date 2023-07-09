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

# This helper script tags a release using the GitHub API.
#
# https://docs.github.com/en/rest/reference/repos#create-a-release

import os
import sys
import json

import requests

from pyvcg.version import PYVCG_VERSION
import util.changelog

def main():
    username = os.environ.get("GITHUB_USERNAME", None)
    if username is None:
        print("Please set the GITHUB_USERNAME environment variable")

    token = os.environ.get("GITHUB_PYVCG_TOKEN", None)
    if token is None:
        print("Please set the GITHUB_PYVCG_TOKEN environment variable")

    if username is None or token is None:
        sys.exit(1)

    auth = requests.auth.HTTPBasicAuth(username, token)

    api_endpoint = "https://api.github.com/repos/%s/%s/releases" % \
        ("florianschanda", "pyvcg")

    tag_name = "pyvcg-%s" % PYVCG_VERSION
    rel_name = "Release %s" % PYVCG_VERSION
    rel_body = "### %s\n\n%s" % (PYVCG_VERSION,
                                 util.changelog.current_section())

    data = {"tag_name" : tag_name,
            "name"     : rel_name,
            "body"     : rel_body}

    r = requests.post(api_endpoint, auth=auth, data=json.dumps(data))
    print(r)

if __name__ == "__main__":
    main()
