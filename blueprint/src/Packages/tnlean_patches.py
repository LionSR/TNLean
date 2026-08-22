"""TNLean-local additions to the shared texra_patches plasTeX package.

The shared patch layer lives in the ``texra_blueprint`` plugin; this shim
carries only what is TNLean's own: the repair map entry for a ``\\lean``
declaration observed mangled in #398.  The ``\\tenkzkernel`` declaration is
registered by ``tenkz_pic``.
"""

from texra_blueprint.Packages.texra_patches import DECL_REPLACEMENTS

# In-place mutation of the plugin's module-level dict is the documented
# extension point at the pinned texra-blueprint version; a version bump
# must re-verify that DECL_REPLACEMENTS stays a plain mutable dict.

DECL_REPLACEMENTS["MPSTensor.exponentialconvergenceofprimitive"] = (
    "MPSTensor.exponential_convergence_of_primitive"
)
