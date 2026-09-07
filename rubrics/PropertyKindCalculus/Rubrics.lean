/-
# PropertyKindCalculus.Rubrics

The **application-template** layer: what a document that *applies* the calculus must
address, and the machinery a downstream document uses to declare — checkably — where
it addresses each item.

`PropertyKindCalculus.Requirements` says what the calculus must do. This layer says
what a domain model built on it, and the deployment of that model, must do. It hosts
no domain content of its own: the templates are generic, and the documents that
answer to them live in their own repositories.

  * `PropertyKindCalculus.Rubrics.Catalogue`  — the two templates: the model template
    (M1–M26) and the deployment template (D1–D17), each rubric carrying the kind of
    evidence that would discharge it.
  * `PropertyKindCalculus.Rubrics.Attributes` — the `@[rubric …]` declaration-site
    attribute, the section-site map, and the derived conformance status.
-/

import PropertyKindCalculus.Rubrics.Catalogue
import PropertyKindCalculus.Rubrics.Attributes
