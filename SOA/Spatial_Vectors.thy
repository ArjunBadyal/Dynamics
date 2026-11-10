theory Spatial_Vectors
imports Vector_Derivatives
begin

section \<open> Spatial vectors \<close>


type_synonym spatial_vector = "(real^3) \<times> (real^3)"


definition has_spatial_velocity :: "(real \<Rightarrow> frame) \<Rightarrow> spatial_vector \<Rightarrow> real \<Rightarrow> bool" where
"has_spatial_velocity X V t \<longleftrightarrow>
has_angular_velocity (\<lambda>s. \<^bold>I) X (fst V) t \<and> has_linear_velocity X (snd V) t"

section \<open> The cross product for spatial vectors \<close>

(* Jain, equation (1.23) *)

fun spatial_cross :: "spatial_vector \<Rightarrow> spatial_vector \<Rightarrow> spatial_vector" (infixr \<open>\<otimes>\<close> 80) where
"(x, y) \<otimes> (a, b) = (x \<times> a, y \<times> a + x \<times> b)"

(* Jain, equation (1.24) *)

lemma spatial_cross_refl: "A \<otimes> A = 0"
by (cases A) (simp add: zero_prod_def cross3_simps)

lemma spatial_cross_skew: "A \<otimes> B = - (B \<otimes> A)"
by (cases A, cases B) (simp add: cross3_simps)

lemma spatial_cross_Jacobi: "A \<otimes> (B \<otimes> C) + B \<otimes> (C \<otimes> A) + C \<otimes> (A \<otimes> B) = 0"
by (cases A, cases B, cases C) (simp add: zero_prod_def cross3_simps)

end
