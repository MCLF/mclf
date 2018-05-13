# Monkey patches for Sage 8.2
import sage.all

# https://trac.sagemath.org/ticket/25294
import sage.rings.valuation.valuation
sage.rings.valuation.valuation.DiscreteValuation._original_mac_lane_approximants = sage.rings.valuation.valuation.DiscreteValuation.mac_lane_approximants
def _monkey_mac_lane_approximants(self, *args, **kwargs):
    import inspect
    curframe = inspect.currentframe()
    callframe = inspect.getouterframes(curframe, 2)
    if 'function_field_valuation' in callframe[1][1]:
            if callframe[1][3] in ['create_key_and_extra_args_from_valuation', 'extensions']:
                kwargs.setdefault('require_incomparability', True)
    return sage.rings.valuation.valuation.DiscreteValuation._original_mac_lane_approximants(self, *args, **kwargs)
sage.rings.valuation.valuation.DiscreteValuation.mac_lane_approximants = _monkey_mac_lane_approximants
del _monkey_mac_lane_approximants
