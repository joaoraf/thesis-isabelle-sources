subsection \<open>Twin Spheres Example\<close>

theory TwinSpheresIdentity
  imports  Identifiability "../ParticularStructures/TwinSpheres"
begin

(* 
interpretation conf1_struct: particular_struct conf1 \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  by simp

interpretation conf1: ufo_particular_theory
      \<open>conf1.\<W>\<close> \<open>conf1.inheresIn\<close> \<open>conf1.\<Q>\<S>\<close> \<open>conf1.assoc_quale\<close> \<open>conf1.towards\<close> 
      \<open>TYPE(endurant)\<close> \<open>TYPE(quale)\<close>
  using conf1.ufo_particular_theory_axioms .

find_consts name: "conf1."

term \<open>ufo_particular_theory_sig.identifiables conf1.\<W> conf1.inheresIn conf1.\<Q>\<S>
          conf1.assoc_quale conf1.towards\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> conf1_sphere1_identifiable: \<open>Sphere1 \<in> conf1.identifiables\<close>
  apply (simp only: conf1.identifiable_particulars_are_the_non_permutables)
  apply (intro conf1.non_permutables_I)
  subgoal G1 by (auto simp: all_defs)
proof (intro conf1.non_permutable_I)
  fix \<phi> y
  assume \<open>\<phi> \<in> EndoMorphs\<^bsub>conf1.\<Gamma>\<^esub>\<close> \<open>y \<in> conf1.\<P>\<close>
  then interpret phi: particular_struct_endomorphism \<open>conf1.\<Gamma>\<close> \<phi>
    using endomorphisms_D[of \<phi>] by metis  
  have A: \<open>conf1.inheresIn Sphere1Radius10M Sphere1\<close> 
      \<open>conf1.assoc_quale Sphere1Radius10M Q_Radius10M\<close>
    by (simp add: all_defs)+
  note B = phi.morph_closes_quale_assoc[of \<open>conf1.\<w>\<close> Sphere1 \<open>\<phi> Sphere1Radius10M\<close> Q_Radius10M
        , simplified]
  show \<open>\<phi> y = Sphere1 \<longleftrightarrow> y = Sphere1\<close>
    apply (cases y ; simp)
    
    oops
*)

end