theory Configuration_Space
  imports "Smooth_Manifolds.Differentiable_Manifold"
begin

text \<open>A configuration space is, most abstractly, a C-infinity manifold (cf. Abraham and Marsden, pp. 32--33).\<close>

locale configuration_space =
  c_manifold charts \<infinity>
  for charts ::
    "('q::{t2_space, second_countable_topology}, 'e::euclidean_space) chart set"

end
