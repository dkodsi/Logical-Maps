import Classicism.Semantics.Research.CentralSupportedProductNegative
import Classicism.Semantics.Research.CentralChoice

/-!
# Choice in the concrete supported product

The actual pure model and its choice properties, isolated from the separate
finitary-syntax/gluing proof of Logical Necessity. Existing source:
`research/2026-10-22/followup/central-map.md`, §§1–3.
-/

namespace Classicism.Meta.Intensional.Central.Product
open CategoryTheory

variable (I L : Type)

theorem model_extFull {Sig : Signature}
    (J : ∀ c : Sig.Const, (domain I L (Sig.typeOf c)).obj (star I L)) :
    (model I L J).ExtFull :=
  Central.model_extFull (control I L) (individuals I L) (star I L) _ J

theorem pure_holds_box_rc (σ τ : Ty) :
    (pureModel I L).HoldsSentence (P.NecRelationalChoice.quoted σ τ) :=
  Premodel.holds_box_rc (model_isModel I L _) (model_extFull I L _) (𝟙 _) σ τ

theorem pure_holds_tc (σ : Ty) :
    (pureModel I L).HoldsSentence (P.TransversalChoice.quoted σ) :=
  Premodel.holds_tc (model_isModel I L _) (model_extFull I L _) (𝟙 _) σ

end Classicism.Meta.Intensional.Central.Product
