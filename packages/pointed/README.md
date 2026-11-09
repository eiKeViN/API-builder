# PointedRecipes

Independent Lake provider built against the public SDK frozen at
`2e8d5a31561221b549f6f79619dd580f6b97fb6f`.
No files under `ApiBuilder/` were changed to implement it.

The local Lake dependency is `apiBuilder` at `../..`. Use the repository's pinned
Lean/mathlib manifest. `Target.lean` reexports the actual mathlib Pointed target;
`Recipes.lean` public-meta-imports only the documented bundled-map SDK facade.

`pointedMap : ApiBuilder.Recipe` calls public `prepareBundledMap`, decodes two new
named fields (`point`, `preserves_point`), adds five owned outputs, sequences the
base execution and bridge declarations, and adds a named constructor validator.
The base decoder accepts these extension fields because the dispatcher performs
the final unused-field check only after the complete preparation returns.

The new roles are map_point, toPointedHom, toPointedHom_apply, toPointedHom_id and
toPointedHom_comp. Only map_point and toPointedHom_apply get simp registrations.
The composition theorem intentionally reverses arguments for Pointed.Hom.comp.

Consumers: `../../tests/extended`. Ordinary clients need no meta provider import;
explicit receipt checking needs `meta import PointedRecipes.Recipes`.

The same agent authored SDK and provider. The frozen-source/public-interface test
is real; it is not independent-author usability evidence. No undocumented private
SDK access was required. The fixture's internal Order map_point proof field had to
be named map_point' to reserve the requested public theorem; the dispatcher first
reported this collision rather than silently binding it.
