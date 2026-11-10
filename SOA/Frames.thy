theory Frames
imports "HOL-Analysis.Analysis"
begin

section \<open> Coordinate frames \<close>

(* Coordinate-free vectors are modeled by real^3 in the inertial frame. *)

typedef rotation = "{R :: real^3^3. rotation_matrix R}"
morphisms rotation_matrix_of Abs_rotation
by (rule exI[of _ "mat 1"]) (simp add: rotation_matrix_def orthogonal_matrix_id)

declare [[coercion rotation_matrix_of]]

record frame =
origin :: "real^3"
attitude :: rotation

definition coords :: "frame \<Rightarrow> real^3 \<Rightarrow> real^3" (\<open>\<^bsup>_\<^esup>_\<close> [0, 1000]) where
"\<^bsup>F\<^esup>x = transpose (attitude F) *v x"

definition rot :: "frame \<Rightarrow> frame \<Rightarrow> real^3^3" (\<open>\<^bsup>_\<^esup>\<^bold>R\<^bsub>_\<^esub>\<close> [0, 0]) where
"\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> = transpose (attitude F) ** attitude G"

definition offset :: "frame \<Rightarrow> frame \<Rightarrow> real^3" (\<open>\<^bold>l'(_,/ _')\<close> [0, 0]) where
"\<^bold>l(F, G) = origin G - origin F"

definition position :: "frame \<Rightarrow> real^3 \<Rightarrow> real^3" (\<open>\<^bold>p'(_,/ _')\<close> [0, 0]) where
"\<^bold>p(F, y) = y - origin F"

lemma rotation_transpose_mult [simp]:
fixes A :: rotation
shows "transpose A ** (A :: real^3^3) = mat 1" "(A :: real^3^3) ** transpose A = mat 1"
using rotation_matrix_of[of A] by (simp_all add: rotation_matrix_def orthogonal_matrix_def)

lemma rot_rotation_matrix: "rotation_matrix (\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub>)"
using rotation_matrix_of[of "attitude F"] rotation_matrix_of[of "attitude G"]
by (simp add: rot_def rotation_matrix_def orthogonal_matrix_mul det_mul)

lemma rot_transpose: "transpose (\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub>) = \<^bsup>G\<^esup>\<^bold>R\<^bsub>F\<^esub>"
by (simp add: rot_def matrix_transpose_mul)

lemma rot_rot: "\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> ** \<^bsup>G\<^esup>\<^bold>R\<^bsub>H\<^esub> = \<^bsup>F\<^esup>\<^bold>R\<^bsub>H\<^esub>"
by (metis rot_def matrix_mul_assoc matrix_mul_lid rotation_transpose_mult(2))

lemma coords_add: "\<^bsup>F\<^esup>(x + y) = \<^bsup>F\<^esup>x + \<^bsup>F\<^esup>y"
by (simp add: coords_def matrix_vector_right_distrib del: transpose_matrix_vector)

lemma coords_neg: "\<^bsup>F\<^esup>(- x) = - \<^bsup>F\<^esup>x"
by (simp add: coords_def linear_neg[OF matrix_vector_mul_linear] del: transpose_matrix_vector)

lemma rot_coords: "\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> *v \<^bsup>G\<^esup>x = \<^bsup>F\<^esup>x"
by (metis coords_def rot_def matrix_vector_mul_assoc matrix_mul_assoc matrix_vector_mul_lid
matrix_mul_rid rotation_transpose_mult(2))

(* Jain, equations (1.1) and (1.2) *)

lemma position_offset: "\<^bold>p(F, y) = \<^bold>l(F, G) + \<^bold>p(G, y)"
by (simp add: position_def offset_def)

lemma coords_position: "\<^bsup>F\<^esup>\<^bold>p(F, y) = \<^bsup>F\<^esup>\<^bold>l(F, G) + \<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub> *v \<^bsup>G\<^esup>\<^bold>p(G, y)"
by (simp add: rot_coords position_offset[of F y G] coords_add)

section \<open> Homogeneous transforms \<close>

(* Jain, equations (1.3) and (1.4) *)

datatype htransform = HT (ht_rot: "real^3^3") (ht_off: "real^3")

definition htrans :: "frame \<Rightarrow> frame \<Rightarrow> htransform" (\<open>\<^bsup>_\<^esup>\<^bold>T\<^bsub>_\<^esub>\<close> [0, 0]) where
"\<^bsup>F\<^esup>\<^bold>T\<^bsub>G\<^esub> = HT (\<^bsup>F\<^esup>\<^bold>R\<^bsub>G\<^esub>) (\<^bsup>F\<^esup>\<^bold>l(F, G))"

definition ht_apply :: "htransform \<Rightarrow> real^3 \<Rightarrow> real^3" (infixl \<open>*\<^sub>h\<close> 70) where
"T *\<^sub>h p = ht_off T + ht_rot T *v p"

lemma htrans_apply: "\<^bsup>F\<^esup>\<^bold>T\<^bsub>G\<^esub> *\<^sub>h \<^bsup>G\<^esup>\<^bold>p(G, y) = \<^bsup>F\<^esup>\<^bold>p(F, y)"
by (simp add: htrans_def ht_apply_def coords_position[of F y G])

(* Jain, equation (1.5) *)

definition ht_compose :: "htransform \<Rightarrow> htransform \<Rightarrow> htransform" where
"ht_compose S T = HT (ht_rot S ** ht_rot T) (ht_off S + ht_rot S *v ht_off T)"

definition ht_inverse :: "htransform \<Rightarrow> htransform" where
"ht_inverse T = HT (transpose (ht_rot T)) (- (transpose (ht_rot T) *v ht_off T))"

lemma htrans_inverse: "ht_inverse (\<^bsup>F\<^esup>\<^bold>T\<^bsub>G\<^esub>) = \<^bsup>G\<^esup>\<^bold>T\<^bsub>F\<^esub>"
by (simp add: htrans_def ht_inverse_def rot_transpose rot_coords coords_neg[symmetric] offset_def)

lemma htrans_compose: "ht_compose (\<^bsup>F\<^esup>\<^bold>T\<^bsub>G\<^esub>) (\<^bsup>G\<^esup>\<^bold>T\<^bsub>H\<^esub>) = \<^bsup>F\<^esup>\<^bold>T\<^bsub>H\<^esub>"
by (simp add: htrans_def ht_compose_def rot_rot rot_coords coords_add[symmetric] offset_def)

end
