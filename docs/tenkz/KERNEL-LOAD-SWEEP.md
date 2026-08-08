# Kernel load-time binding sweep

This is the 2026-07-28 audit requested by #5014, now historical: the S4
surface swap has executed and `tenkz.sty` binds the kernel surface at load
(`r_load_surface.tex` pins the post-swap contract). The audit below recorded
the pre-swap boundary, when the 1.0 kernel was a group-local opt-in and
loading the package could not change the 0.7 command surface.

## Method

The sweep used two views of `tenkz-kernel.code.tex`.

1. A source inventory covered every file-scope `\cs_new...`,
   `\NewDocumentCommand`, `\cs_generate_variant`, `\keys_define`, and shared
   assignment.
2. A LuaTeX hash-table snapshot loaded all 0.7 stages without the kernel,
   recorded every control-sequence meaning, then input the kernel and compared
   the complete table. The same pass inspected generated l3keys control
   sequences; a source search confirmed that the kernel creates no pgfkeys
   paths.

Undefined names interned while the kernel source was tokenized were not counted
as bindings. LaTeX3 command/key-definition scratch registers changed transient
values during input; they are framework-owned scratch, and no tenkz dialect
reads them.

## Result

| Name or class | Binding time | Owner | Verdict |
|---|---|---|---|
| `\tenkzkernel` | package load | kernel public entry point | Keep. This is the sole public kernel command defined by loading the stage. |
| `\tnwire`, `\tnmark`, `\tndeclare`, `\tnbond`, `\tnprose` | formerly package load; now `\tenkzkernel` | kernel body grammar | Load-time leak fixed. Their implementations are private and the switch binds the public names for its group. |
| `tenkzeq`, `\endtenkzeq` | formerly no-op placeholders at package load; now `\tenkzkernel` | kernel equation grammar | Load-time leak fixed. The silent placeholders were removed. |
| `tenkz`, `\endtenkz`, `\tnset`, `\tngroup` | `\tenkzkernel` | shared 0.7 names | Safe. The switch changes them locally and group exit restores the exact prior meanings. |
| `\tn` and row `\\` | kernel picture begin | shared dialect names | Safe. The environment group owns and restores them. |
| `\__tenkz_kernel_...` plus `\l__tenkz_kernel_...`, `\g__tenkz_kernel_...`, and `\c__tenkz_kernel_...` | package load | kernel private implementation and state | Safe. The hash-table additions are name-mangled and do not replace a prior meaning. |
| l3keys trees `tenkz-kernel-picture`, `tenkz-kernel-atom`, `tenkz-kernel-wire`, and `tenkz-kernel-setup` | package load | kernel parser | Safe. Every generated handler remains in a kernel-owned tree; the kernel defines no pgfkeys path. |
| geometry/render variants used by the kernel | owning stage load | shared geometry/render services | Boundary fixed. Variant declarations moved from the kernel file to the stage that owns each base function. |
| commands created by `\tndeclare{atom}` | explicit declaration | author-requested kernel extension | Safe. They are runtime output of the documented extension door, not package-load state. |

The post-fix hash comparison found no changed 0.7 command or environment
meaning and no kernel-created control sequence in another tenkz stage's
namespace. `tests/tenkz/kernel/regression/r_load_inert.tex` makes the public
part of that result permanent: the kernel body/equation names are absent
before opt-in, present inside the switch group, absent again afterward, and
the saved 0.7 `tenkz`, `tnset`, and `tngroup` meanings are restored exactly.

## Gates

Run:

```sh
scripts/tenkz_kernel_probes.sh
scripts/tenkz_corpus.sh
```

The first command includes the load-inertness regression and the kernel event
and pixel goldens. The second keeps the bridge byte-identical for the complete
0.7 fixture corpus.
