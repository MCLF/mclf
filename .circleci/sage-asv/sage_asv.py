# Licensed under a 3-clause BSD style license - see LICENSE.rst
# -*- coding: utf-8 -*-
import asv
import os.path
import sys

class Sage(asv.environment.Environment):
    tool_name = "sage"

    def __init__(self, conf, executable, requirements, tagged_env_vars):
        self._executable = sys.executable
        executable = os.path.abspath(asv.util.which(self._executable))
        self._requirements = {}
        self._python = asv.util.check_output(
            [executable,
             '-c',
             'import sys; '
             'print(str(sys.version_info[0]) + "." + str(sys.version_info[1]))'
             ]).strip()
        super(Sage, self).__init__(conf, executable, requirements, tagged_env_vars)

    @classmethod
    def matches(cls, python):
        if python == 'same':
            python = sys.executable

        try:
            asv.util.which(python)
        except IOError:
            return False
        else:
            return True

    @property
    def name(self):
        return asv.environment.get_env_name(self.tool_name,
                            self._executable.replace(os.path.sep, '_'),
                            {})

    def check_presence(self):
        return True

    def create(self):
        pass

    def _setup(self):
        pass

    def install_project(self, conf, repo, commit_hash=None):
        pass

    def can_install_project(self):
        return False

    def run(self, args, **kwargs):
        asv.console.log.debug("Running '{0}' in {1}".format(' '.join(args), self.name))
        return asv.util.check_output([
            self._executable] + args, **kwargs)
