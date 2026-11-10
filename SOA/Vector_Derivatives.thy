theory Vector_Derivatives
imports Frames
begin

(* Jain, Sect. 1.2. From here on x \<times> y is the cross product of HOL-Analysis, which Jain writes
   as x \<otimes> y. This turns off the same notation for products of sets. *)

unbundle cross3_syntax

section \<open> The cross product \<close>

(* Jain, equations (1.9) and (1.10) *)

definition tilde :: "real^3 \<Rightarrow> real^3^3" (\<open>_\<^sup>~\<close> [1000] 999) where
"l\<^sup>~ = vector [vector [0, - l$3, l$2], vector [l$3, 0, - l$1], vector [- l$2, l$1, 0]]"

lemma tilde_cross: "l\<^sup>~ *v x = l \<times> x"
by (simp add: tilde_def cross3_def matrix_vector_mult_def vec_eq_iff forall_3 sum_3)

lemma coords_zero [simp]: "\<^bsup>F\<^esup>0 = 0"
by (simp add: coords_def)

lemma coords_cross: "\<^bsup>F\<^esup>(x \<times> y) = \<^bsup>F\<^esup>x \<times> \<^bsup>F\<^esup>y"
proof -
  have "rotation_matrix (transpose (attitude F))"
    using rotation_matrix_of[of "attitude F"]
    by (simp add: rotation_matrix_def orthogonal_matrix_def)
  then show ?thesis
    by (simp add: coords_def cross_rotation_matrix del: transpose_matrix_vector)
qed

section \<open> Two facts for differentiating products with matrices \<close>

lemma bounded_bilinear_matrix_vector:
"bounded_bilinear ((*v) :: real^'n^'m \<Rightarrow> real^'n \<Rightarrow> real^'m)"
by (rule bilinear_conv_bounded_bilinear[THEN iffD1])
  (auto simp: bilinear_def linear_iff matrix_vector_right_distrib matrix_vector_mult_add_rdistrib
    scaleR_matrix_vector_assoc[symmetric] matrix_vector_mult_scaleR)

lemma bounded_linear_matrix_mult_left:
fixes C :: "real^3^3"
shows "bounded_linear (\<lambda>A :: real^3^3. A ** C)"
proof -
  have "(A + B) ** C = A ** C + B ** C" for A B :: "real^3^3"
    by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)
  then show ?thesis
    by (intro linear_conv_bounded_linear[THEN iffD1]) (simp add: linear_iff scalar_matrix_assoc)
qed

section \<open> Derivatives observed in a frame \<close>

(* A moving frame is a function from time to frames. Jain, equation (1.6): x' is the derivative
   of x observed in F at time t when the representation of x' in F is the derivative of the
   representation of x in F. *)

definition has_frame_derivative ::
"(real \<Rightarrow> frame) \<Rightarrow> (real \<Rightarrow> real^3) \<Rightarrow> real^3 \<Rightarrow> real \<Rightarrow> bool" where
"has_frame_derivative F x x' t \<longleftrightarrow>
((\<lambda>s. \<^bsup>F s\<^esup>(x s)) has_vector_derivative \<^bsup>F t\<^esup>x') (at t)"

(* Jain, equation (1.8): w is the angular velocity of G with respect to F at time t *)

definition has_angular_velocity ::
"(real \<Rightarrow> frame) \<Rightarrow> (real \<Rightarrow> frame) \<Rightarrow> real^3 \<Rightarrow> real \<Rightarrow> bool" where
"has_angular_velocity F G w t \<longleftrightarrow>
((\<lambda>s. \<^bsup>F s\<^esup>\<^bold>R\<^bsub>G s\<^esub>) has_vector_derivative (\<^bsup>F t\<^esup>w)\<^sup>~ ** \<^bsup>F t\<^esup>\<^bold>R\<^bsub>G t\<^esub>) (at t)"

(* The second equality in (1.8) *)

lemma tilde_rot: "(\<^bsup>F\<^esup>w)\<^sup>~ ** \<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> = \<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> ** (\<^bsup>G\<^esup>w)\<^sup>~"
proof -
  have "((\<^bsup>F\<^esup>w)\<^sup>~ ** \<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub>) *v x = (\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> ** (\<^bsup>G\<^esup>w)\<^sup>~) *v x" for x
    using cross_rotation_matrix[OF rot_rotation_matrix, of F G "\<^bsup>G\<^esup>w" x]
    by (simp add: matrix_vector_mul_assoc[symmetric] tilde_cross rot_coords)
  then show ?thesis
    by (simp add: matrix_eq)
qed

(* Jain, equations (1.11) and (1.12) *)

theorem frame_derivative_change:
assumes "has_angular_velocity F G w t" and "has_frame_derivative G x x' t"
shows "has_frame_derivative F x (x' + w \<times> x t) t"
proof -
  have "((\<lambda>s. \<^bsup>F s\<^esup>\<^bold>R\<^bsub>G s\<^esub> *v \<^bsup>G s\<^esup>(x s)) has_vector_derivative
      \<^bsup>F t\<^esup>\<^bold>R\<^bsub>G t\<^esub> *v \<^bsup>G t\<^esup>x' + ((\<^bsup>F t\<^esup>w)\<^sup>~ ** \<^bsup>F t\<^esup>\<^bold>R\<^bsub>G t\<^esub>) *v \<^bsup>G t\<^esup>(x t)) (at t)"
    using assms unfolding has_angular_velocity_def has_frame_derivative_def
    by (rule bounded_bilinear.has_vector_derivative[OF bounded_bilinear_matrix_vector])
  then show ?thesis
    by (simp add: has_frame_derivative_def rot_coords matrix_vector_mul_assoc[symmetric]
        tilde_cross coords_add coords_cross)
qed

section \<open> Rigid body vector derivatives \<close>

(* The inertial frame. Representations in it are the vectors themselves. *)

definition inertial :: frame (\<open>\<^bold>I\<close>) where
"\<^bold>I = \<lparr>origin = 0, attitude = Abs_rotation (mat 1)\<rparr>"

lemma origin_inertial [simp]: "origin \<^bold>I = 0"
by (simp add: inertial_def)

lemma attitude_inertial [simp]: "rotation_matrix_of (attitude \<^bold>I) = mat 1"
by (simp add: inertial_def Abs_rotation_inverse rotation_matrix_def orthogonal_matrix_id)

lemma coords_inertial [simp]: "\<^bsup>\<^bold>I\<^esup>x = x"
by (simp add: coords_def)

lemma rot_inertial [simp]: "\<^bsup>\<^bold>I\<^esup>\<^bold>R\<^bsub>G\<^esub> = attitude G"
by (simp add: rot_def)

(* Observed in the inertial frame, (1.6) is the ordinary derivative and (1.8) is dR/dt = w~ R *)

lemma has_frame_derivative_inertial:
"has_frame_derivative (\<lambda>s. \<^bold>I) x x' t \<longleftrightarrow> (x has_vector_derivative x') (at t)"
by (simp add: has_frame_derivative_def)

lemma has_angular_velocity_inertial:
"has_angular_velocity (\<lambda>s. \<^bold>I) X w t \<longleftrightarrow>
((\<lambda>s. rotation_matrix_of (attitude (X s))) has_vector_derivative w\<^sup>~ ** attitude (X t)) (at t)"
by (simp add: has_angular_velocity_def)

(* Jain, the definition before (1.15): the linear velocity of a moving frame is the derivative of
   its position observed in the inertial frame *)

definition has_linear_velocity :: "(real \<Rightarrow> frame) \<Rightarrow> real^3 \<Rightarrow> real \<Rightarrow> bool" where
"has_linear_velocity X v t \<longleftrightarrow> has_frame_derivative (\<lambda>s. \<^bold>I) (\<lambda>s. \<^bold>l(\<^bold>I, X s)) v t"

lemma has_linear_velocity_iff:
"has_linear_velocity X v t \<longleftrightarrow> ((\<lambda>s. origin (X s)) has_vector_derivative v) (at t)"
by (simp add: has_linear_velocity_def has_frame_derivative_def offset_def)

(* Frames fixed to the same rigid body keep a constant relative position and attitude *)

definition rigidly_attached :: "(real \<Rightarrow> frame) \<Rightarrow> (real \<Rightarrow> frame) \<Rightarrow> bool" where
"rigidly_attached X Y \<longleftrightarrow> (\<exists>C. \<forall>s. \<^bsup>X s\<^esup>\<^bold>T\<^bsub>Y s\<^esub> = C)"

(* Jain, equation (1.15) *)

lemma rigid_body_linear_velocity:
assumes "rigidly_attached X Y" and "has_angular_velocity (\<lambda>s. \<^bold>I) X w t"
and "has_linear_velocity X v t"
shows "has_linear_velocity Y (v + w \<times> \<^bold>l(X t, Y t)) t"
proof -
  obtain C where C: "\<And>s. \<^bsup>X s\<^esup>\<^bold>T\<^bsub>Y s\<^esub> = C"
    using assms(1) by (auto simp: rigidly_attached_def)
  have "\<^bsup>X s\<^esup>\<^bold>l(X s, Y s) = ht_off C" for s
    using C[of s] by (auto simp: htrans_def)
  then have "has_frame_derivative X (\<lambda>s. \<^bold>l(X s, Y s)) 0 t"
    by (simp add: has_frame_derivative_def)
  from frame_derivative_change[OF assms(2) this]
  have "((\<lambda>s. \<^bold>l(X s, Y s)) has_vector_derivative w \<times> \<^bold>l(X t, Y t)) (at t)"
    by (simp add: has_frame_derivative_def)
  from has_vector_derivative_add[OF assms(3)[unfolded has_linear_velocity_iff] this]
  show ?thesis
    by (simp add: has_linear_velocity_iff offset_def)
qed

(* Jain, equation (1.16) *)

lemma rigid_body_angular_velocity:
assumes "rigidly_attached X Y" and "has_angular_velocity F X w t"
shows "has_angular_velocity F Y w t"
proof -
  obtain C where C: "\<And>s. \<^bsup>X s\<^esup>\<^bold>T\<^bsub>Y s\<^esub> = C"
    using assms(1) by (auto simp: rigidly_attached_def)
  have R: "\<^bsup>F s\<^esup>\<^bold>R\<^bsub>Y s\<^esub> = \<^bsup>F s\<^esup>\<^bold>R\<^bsub>X s\<^esub> ** ht_rot C" for s
    using C[of s] rot_rot[of "F s" "X s" "Y s"] by (auto simp: htrans_def)
  have "((\<lambda>s. \<^bsup>F s\<^esup>\<^bold>R\<^bsub>X s\<^esub> ** ht_rot C) has_vector_derivative
      ((\<^bsup>F t\<^esup>w)\<^sup>~ ** \<^bsup>F t\<^esup>\<^bold>R\<^bsub>X t\<^esub>) ** ht_rot C) (at t)"
    using assms(2) unfolding has_angular_velocity_def
    by (rule bounded_linear.has_vector_derivative[OF bounded_linear_matrix_mult_left])
  then show ?thesis
    by (simp add: has_angular_velocity_def R matrix_mul_assoc)
qed

end
