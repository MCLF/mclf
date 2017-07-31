"""  Valuation trees

"""



Class MacLanePseudoValuation(SageObject):
    """ Create a MacLane pseudo valuation on rational function field.
    """

    def __init__(self, F, v):
        """ Create a MacLane pseudo valuation on rational function field.

        INPUT:

        - F: a rational function field over a discretly valued field
        - v: either a MacLane valuation on F, or a pair (v1,v2), where
             v1 is a function field valuation on F and v2 is an extension
             of the base valuation to th residue field of v1

        OUTPUT:

        The MacLane pseudo valuation on F corresponding to v rsp. (v1,v2)

        """

        pass

    def __repr__(self):

        pass

    def is_valuation(self):
        """ Returns True if self is a valuation.
        """

        return self._is_valuation()

    def eval(self, f):
        """ Return self(f).
        """
