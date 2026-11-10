theory Rigid_Body_Transformation
imports Spatial_Vectors
begin

section \<open> The rigid body transformation matrix \<close>

(* Jain, equation (1.29) *)

definition rbt :: "frame \<Rightarrow> frame \<Rightarrow> spatial_vector \<Rightarrow> spatial_vector" (\<open>\<^bold>\<phi>'(_,/ _')\<close> [0, 0]) where
"\<^bold>\<phi>(x, y) = (\<lambda>(a, b). (a + \<^bold>l(x, y) \<times> b, b))"

(* Jain, Lemma 1.1, equation (1.32) *)

lemma rbt_refl: "\<^bold>\<phi>(x, x) = id"
by (simp add: rbt_def offset_def fun_eq_iff)

lemma rbt_rbt: "\<^bold>\<phi>(x, y) \<circ> \<^bold>\<phi>(y, z) = \<^bold>\<phi>(x, z)"
by (simp add: rbt_def offset_def fun_eq_iff cross_add_left[symmetric])

lemma rbt_inverse: "inv (\<^bold>\<phi>(x, y)) = \<^bold>\<phi>(y, x)"
by (rule inv_unique_comp) (simp_all add: rbt_rbt rbt_refl)

lemma linear_rbt: "linear (\<^bold>\<phi>(x, y))"
by (auto simp: linear_iff rbt_def cross_add_right cross_mult_right scaleR_add_right)

(* The transpose of \<phi>(x, y), shown after (1.33) *)

definition rbt_adj :: "frame \<Rightarrow> frame \<Rightarrow> spatial_vector \<Rightarrow> spatial_vector" (\<open>\<^bold>\<phi>\<^sup>*'(_,/ _')\<close> [0, 0]) where
"\<^bold>\<phi>\<^sup>*(x, y) = (\<lambda>(a, b). (a, b - \<^bold>l(x, y) \<times> a))"

lemma rbt_adjoint: "\<^bold>\<phi>(x, y) f \<bullet> V = f \<bullet> \<^bold>\<phi>\<^sup>*(x, y) V"
by (cases f, cases V) (simp add: rbt_def rbt_adj_def cross3_simps)

lemma adjoint_rbt: "adjoint (\<^bold>\<phi>(x, y)) = \<^bold>\<phi>\<^sup>*(x, y)"
by (rule adjoint_unique) (simp add: rbt_adjoint)

lemma linear_rbt_adj: "linear (\<^bold>\<phi>\<^sup>*(x, y))"
by (auto simp: linear_iff rbt_adj_def cross_add_right cross_mult_right scaleR_diff_right)

lemma rbt_adj_refl: "\<^bold>\<phi>\<^sup>*(x, x) = id"
by (simp add: rbt_adj_def offset_def fun_eq_iff)

lemma rbt_adj_rbt_adj: "\<^bold>\<phi>\<^sup>*(y, z) \<circ> \<^bold>\<phi>\<^sup>*(x, y) = \<^bold>\<phi>\<^sup>*(x, z)"
by (simp add: rbt_adj_def offset_def fun_eq_iff Cross3.left_diff_distrib)

section \<open> Spatial velocity transformations \<close>

(* Jain, equation (1.33) *)

theorem spatial_velocity_transform:
assumes "rigidly_attached X Y" and "has_spatial_velocity X V t"
shows "has_spatial_velocity Y (\<^bold>\<phi>\<^sup>*(X t, Y t) V) t"
proof -
  obtain w v where V: "V = (w, v)"
    by (cases V)
  have "w \<times> \<^bold>l(X t, Y t) = - (\<^bold>l(X t, Y t) \<times> w)"
    by (rule cross_skew)
  then show ?thesis
    using assms rigid_body_angular_velocity[of X Y "\<lambda>s. \<^bold>I" w t]
      rigid_body_linear_velocity[of X Y w t v]
    by (simp add: has_spatial_velocity_def rbt_adj_def V)
qed

section \<open> Spatial forces \<close>

(* Jain, Sect. 1.5. A spatial force is a spatial vector (N, F) of a moment and a linear force,
   equation (1.46). The power it produces with a spatial velocity V is the inner product f \<bullet> V. *)

(* Jain, equation (1.47): the power is the same at x and at y for every spatial velocity exactly
   when the spatial forces are related by \<phi>(x, y) *)

theorem spatial_force_transform:
"(\<forall>V. fx \<bullet> V = fy \<bullet> \<^bold>\<phi>\<^sup>*(x, y) V) \<longleftrightarrow> fx = \<^bold>\<phi>(x, y) fy"
by (simp only: rbt_adjoint[symmetric] vector_eq_rdot)

end
