/-
# PropertyKindCalculus.Terminology

The **terminological dictionary**: one entry per concept the calculus names, carrying the
canonical phrase, its sanctioned short form, a one-sentence gloss, the declarations that
carry the concept, the blueprint section that defines the term, and the retired phrasings
that must not reappear.

The dictionary exists for communication, not for branding: a reader who meets three
phrases for one object concludes there are three objects. So every concept has one name,
the name is defined in exactly one place in the blueprint, and every other document —
blueprint chapters, the root plan documents, and, by ratchet, the library's own
docstrings — uses that name or its short form. `PropertyKindCalculus.Terminology.Dictionary`
is the data; the blueprint's terminology chapter renders it and links each entry to its
defining section; the `doc-pins` gate (`tools/Tools/DocPins.lean`) is the gate.
-/

module

public import PropertyKindCalculus.Terminology.Dictionary

@[expose] public section Blanket



end Blanket
