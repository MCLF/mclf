# -*- coding: utf-8 -*-
r"""
Shared monkey patching utilities
"""
#*****************************************************************************
#       Copyright (C) 2018 Julian Rüth <julian.rueth@fsfe.org>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
#*****************************************************************************


class AbstractMonkey:
    r"""
    Derived monkeys must implement ``_test()`` and ``_patch()`` to test whether
    the feature to be patched has been fixed already and to perform the actual
    patching.

    EXAMPLES::

        sage: from mclf.monkey.util import AbstractMonkey
        sage: class Monkey(AbstractMonkey):
        ....:     _trac = "https://trac.sagemath.org/..."
        ....:     def _test(self):
        ....:         pass # run tests here
        ....:     def _patch(self):
        ....:         pass # call patchy.patch() here

        sage: Monkey().patch()

    When patching fails, we run ``_test()`` to check whether the patch is
    necessary at all::

        sage: class Monkey(AbstractMonkey):
        ....:     _trac = "https://trac.sagemath.org/..."
        ....:     def _test(self):
        ....:         pass # run tests here
        ....:     def _patch(self):
        ....:         raise NotImplementedError("call patchy.patch() here")

        sage: Monkey().patch()

        sage: class Monkey(AbstractMonkey):
        ....:     _trac = "https://trac.sagemath.org/..."
        ....:     def _test(self):
        ....:         raise Exception("test failed")
        ....:     def _patch(self):
        ....:         raise NotImplementedError("call patchy.patch() here")

        sage: Monkey().patch()
        Your installation of Sage has a known issue: https://trac.sagemath.org/.... We tried to install a workaround for this problem but failed to do so. Please make sure that you are using the latest stable version of Sage. If you are using the latest stable version of Sage already, please report this issue at https://github.com/MCLF/mclf/issues including the traceback below.
        Traceback (most recent call last):
        ...
        NotImplementedError: call patchy.patch() here

    We do not trust our patches. Tests are always run to check that
    ``_patch()`` did the right thing::

        sage: from mclf.monkey.util import AbstractMonkey
        sage: class Monkey(AbstractMonkey):
        ....:     _trac = "https://trac.sagemath.org/..."
        ....:     def _test(self):
        ....:         raise Exception("test failed")
        ....:     def _patch(self):
        ....:         pass # call patchy.patch() here

        sage: Monkey().patch()
        Your installation of Sage has a known issue: https://trac.sagemath.org/.... We thought that we had installed a workaround but apparently failed to do so. Please report this issue at https://github.com/MCLF/mclf/issues including the traceback below.
        Traceback (most recent call last):
        ...
        Exception: test failed

    """
    def patch(self):
        r"""
        Run ``_patch()`` with a more pretty error handling.
        """
        try:
            import patchy
            patchy  # silence pyflakes "imported but not used"
        except Exception:
            if not self.is_fixed():
                import warnings
                warnings.warn("Your installation of Sage has a known issue: %s. Please install patchy with `sage -pip install patchy` to fix this problem."%(self._trac,))
                return

        try:
            self._patch()
        except Exception:
            if not self.is_fixed():
                print("Your installation of Sage has a known issue: %s. We tried to install a workaround for this problem but failed to do so. Please make sure that you are using the latest stable version of Sage. If you are using the latest stable version of Sage already, please report this issue at https://github.com/MCLF/mclf/issues including the traceback below." % (self._trac,))
                import traceback
                traceback.print_exc()
        else:
            try:
                self._test()
            except:
                print("Your installation of Sage has a known issue: %s. We thought that we had installed a workaround but apparently failed to do so. Please report this issue at https://github.com/MCLF/mclf/issues including the traceback below." % (self._trac,))
                import traceback
                traceback.print_exc()

    def is_fixed(self):
        r"""
        Return whether ``_test()`` did not throw an exception.
        """
        try:
            self._test()
        except Exception:
            return False
        else:
            return True
