#!/usr/bin/env python3

import re
import sys
import setuptools

from pyvcg import version

gh_root = "https://github.com"
gh_project = "florianschanda/PyVCG"

with open("README.md", "r") as fd:
    long_description = fd.read()

# For the readme to look right on PyPI we need to translate any
# relative links to absolute links to github.
fixes = []
for match in re.finditer(r"\[(.*)\]\((.*)\)", long_description):
    if not match.group(2).startswith("http"):
        fixes.append((match.span(0)[0], match.span(0)[1],
                      "[%s](%s/%s/blob/main/%s)" % (match.group(1),
                                                    gh_root,
                                                    gh_project,
                                                    match.group(2))))

for begin, end, text in reversed(fixes):
    long_description = (long_description[:begin] +
                        text +
                        long_description[end:])

project_urls = {
    "Bug Tracker"   : "%s/%s/issues" % (gh_root, gh_project),
    "Documentation" : "%s/pages/%s/" % (gh_root, gh_project),
    "Source Code"   : "%s/%s"        % (gh_root, gh_project),
}

setuptools.setup(
    name="PyVCG",
    version=version.PYVCG_VERSION,
    author="Florian Schanda",
    author_email="florian@schanda.org.uk",
    description="Verification Condition Generator",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url=project_urls["Source Code"],
    project_urls=project_urls,
    license="GNU General Public License v3",
    packages=["pyvcg", "pyvcg.driver"],
    extras_require={
        "api": ["cvc5==1.3.0"],
    },
    python_requires=">=3.8",
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Operating System :: POSIX :: Linux",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Topic :: Software Development :: Compilers",
    ],
)
