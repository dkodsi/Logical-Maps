# Modal Well-Ordering under necessary Vicinity

OpenAI Codex, 26 October 2026. Direct source: `misc`, this note, unpaginated.

## 1. Exact statements

MWO abbreviates Modal Well-Ordering, RC Relational Choice, and IC Intensional Choice. All principles below are full schemas in the fixed finitary relational
language. A boxed schema means the separately boxed closed instances.
Over C+□Vicinity,

```math
\boxed{\mathrm{MWO}
\quad\longleftrightarrow\quad
\Box RC+IC}
\tag{1}
```

The universal-modal-selector theorem also gives

```math
\boxed{C+\Box\mathrm{Vicinity}:\qquad
MRC\quad\longleftrightarrow\quad
\mathrm{MWO}}
\tag{2}
```

In particular (2) holds over C5. This settles that restricted case,
not the unrestricted bare-C implication MRC⇒Modal Well-Ordering.

## 2. Proof

The [Vicinity choice theorem](../vicinity-relational-choice-transversals.md),
§§2–4, is an implication over C, at every fixed type σ:

```math
\mathrm{Vicinity}+RC_{(\sigma t),\sigma}\Longrightarrow TC_\sigma
```

Its unconditional closed implication may be necessitated. Therefore
□Vicinity+□RC supplies □TC, and the established TC⇒Well-Ordering
implication supplies □Well-Ordering. The existing chooser-of-orders
theorem now applies: □Well-Ordering+IC⇒Modal Well-Ordering. This is
the forward construction in (1).

Conversely, Modal Well-Ordering is persistent, since each witness R
satisfies □WO(R) and its existing witness persists using 4 and
necessitated existential introduction. Thus Modal Well-Ordering
supplies necessary MRC, hence □RC, and also current IC. These are
existing unconditional implications; □Vicinity is not used in this
direction.

For (2), the [universal-modal-selector theorem](universal-modal-selectors.md),
§§2–4, gives MRC⇒□MRC over bare C, hence □RC+IC. Apply (1).
The reverse Modal Well-Ordering⇒MRC is already valid over C.

C5 supplies □Vicinity: its boxed ND premises imply the
necessary instance of ND_t, and necessitating the unconditional
ND_t⇒Vicinity theorem yields □Vicinity. This proves the C5 corollary.

No optional current principle has been necessitated. Necessitation
is applied only to the closed C implication of an already proved
theorem, followed by K and the explicitly boxed premises.

## 3. Sources and unresolved boundary

- New Vicinity+RC⇒TC theorem: linked above, OpenAI Codex,
  26 October 2026, unpaginated.
- New unconditional full MRC persistence: [Universal modal
  selectors](universal-modal-selectors.md), §§2–4, unpaginated.
- [Necessary Well-Ordering and IC imply Modal Well-Ordering](../../../../logical-maps/topics/classicism/results/necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering.yaml),
  the existing native result and its proof.
- [Modal Well-Ordering implies necessary MRC](../../../../logical-maps/topics/classicism/results/modal-well-ordering-implies-necessary-modalized-relational-choice.yaml),
  the existing native result and its proof.

Full MRC is now known to be necessary over bare C. The unrestricted
MRC⇒Modal Well-Ordering question remains unresolved: the proof above
still uses necessary Vicinity to pass from necessary RC to necessary
TC and Well-Ordering. No bare-C RC⇒TC step is asserted.
