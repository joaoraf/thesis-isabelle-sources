(* text_raw \<open>\subsection[Anchoring and Identity]{Anchoring and Identity\isalabel{subsec:anchoring-identity}}\<close> *)

theory AnchoringAndIdentifiability
  imports Anchoring "../ParticularStructures/Permutability" "../ParticularStructures/InverseImageMorphismChoice"
begin

context ufo_particular_theory
begin

text_raw\<open>\par\<close>
text_raw \<open>\subsection[Anchoring and Identifiability]{Anchoring and Identifiability}\<close>
text_raw \<open>\par\<close>
text_raw \<open>\isalabel{subsec:anchoring-identifiability}\<close>
text \<^marker>\<open>tag bodyonly\<close> \<open>
  The Relationship between anchoring and the definitions of identity
  presented so far is given by the following lemmas and theorem, 
  which show that
  being anchored (having at least one anchor) is logically equivalent
  to being non-permutable and, thus, that anchoring can be used
  interchangeably with the other definitions:
\<close>
text_raw\<open>\par\<close>

lemma non_permutable_are_anchored: \<open>\<P>\<^sub>1\<^sub>! \<subseteq> \<P>\<^sub>\<down>\<close>
proof (intro subsetI ; elim non_permutables_E)
  fix x
  assume \<open>x \<in> \<E>\<close> \<open>non_permutable x\<close>
  obtain \<sigma> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>inj \<sigma>\<close> 
    using injection_to_ZF_exist by blast
  interpret sigma: particular_struct_bijection_1 \<Gamma> \<sigma>    
    by (metis \<open>inj \<sigma>\<close> inj_on_subset inj_morph_img_isomorphism 
              UNIV_I inj_on_id subsetI)

  interpret sigma_inv: 
    particular_struct_bijection \<open>MorphImg \<sigma> \<Gamma>\<close> \<Gamma> sigma.inv_morph    
    using sigma.inv_is_bijective_morphism by blast
  
  have \<open>sigma.inv_morph \<in> InjMorphs\<^bsub>MorphImg \<sigma> \<Gamma>,\<Gamma>\<^esub>\<close>
    by (intro injectives_I sigma_inv.particular_struct_injection_axioms)
  then have A: \<open>MorphImg \<sigma> \<Gamma> \<lless>\<^bsub>sigma.inv_morph\<^esub> \<Gamma>\<close>
    by blast 

  have B: \<open>\<sigma> x \<in> sigma_inv.src.endurants\<close>    
    by (simp add: \<open>x \<in> \<E>\<close> sigma.morph_preserves_particulars)

  have C: \<open>\<phi> z = x \<longleftrightarrow> z = \<sigma> x\<close>
    if as: \<open>z \<in> sigma_inv.src.endurants\<close> 
       \<open>\<phi> \<in> Morphs\<^bsub>MorphImg \<sigma> \<Gamma>,\<Gamma>\<^esub>\<close> for \<phi> z
  proof - 
    interpret phi: particular_struct_morphism \<open>MorphImg \<sigma> \<Gamma>\<close> \<Gamma> \<phi>
      using as(2) by blast
    have AA: \<open>\<delta> y = x \<longleftrightarrow> y = x\<close> 
      if \<open>\<delta> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> for y \<delta> 
      using non_permutable_E[OF \<open>non_permutable x\<close>] that by metis
    interpret phi_sigma: particular_struct_morphism \<Gamma> \<Gamma> \<open>\<phi> \<circ> \<sigma>\<close>
      by (intro particular_struct_morphism_comp[of _ \<open>MorphImg \<sigma> \<Gamma>\<close>]
              sigma.particular_struct_morphism_axioms
              phi.particular_struct_morphism_axioms)
    have \<open>particular_struct_endomorphism \<Gamma> (\<phi> \<circ> \<sigma>)\<close> by intro_locales
    then have BB: \<open>\<phi> \<circ> \<sigma> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> by blast
    have CC: \<open>sigma.inv_morph z \<in> \<E>\<close> 
      using sigma_inv.morph_preserves_particulars that(1) by auto
    have DD: \<open>sigma.inv_morph z = x \<longleftrightarrow> z = \<sigma> x\<close>      
      using \<open>x \<in> \<E>\<close> as(1) by fastforce
    have EE: \<open>z = \<sigma> x \<longleftrightarrow> \<phi> (\<sigma> (sigma.inv_morph z)) = x\<close>
      using AA[of \<open>\<phi> \<circ> \<sigma>\<close>, of \<open>sigma.inv_morph z\<close>,
               OF BB,simplified,OF CC] DD 
      by simp
    show ?thesis
      by (simp add: EE as(1))                
  qed
  show \<open>x \<in> \<P>\<^sub>\<down>\<close>
    apply (intro anchored_particulars_I[
                   of \<open>\<sigma> x\<close> \<open>MorphImg \<sigma> \<Gamma>\<close> \<open>sigma.inv_morph\<close>] 
                 anchorsI \<open>x \<in> \<E>\<close> A B)
    using C by metis
qed

lemma anchored_are_non_permutable: \<open>\<P>\<^sub>\<down> \<subseteq> \<P>\<^sub>1\<^sub>!\<close>
proof (intro subsetI ; elim anchored_particulars_E anchorsE 
        ; intro non_permutables_I non_permutable_I 
        ; assumption? ; intro iffI ; hypsubst_thin)
  fix x y and \<Gamma>\<^sub>x :: \<open>('p\<^sub>1,'q) particular_struct\<close> and \<phi> \<phi>' y\<^sub>1
  assume A: \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<close> \<open>\<phi>' \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
  then interpret phi: particular_struct_injection \<open>\<Gamma>\<^sub>x\<close> \<open>\<Gamma>\<close> \<phi>
    by blast
  have phi_in_morphs: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>
    using phi.particular_struct_morphism_axioms by blast
  interpret phi1_auto: particular_struct_endomorphism \<open>\<Gamma>\<close> \<phi>'
    using A(2) by blast
  interpret phi1: particular_struct_morphism \<Gamma> \<Gamma> \<phi>'    
    using phi1_auto.particular_struct_morphism_axioms by blast
  have \<open>particular_struct_morphism \<Gamma>\<^sub>x \<Gamma> (\<phi>' \<circ> \<phi>)\<close>
    apply (intro particular_struct_morphism_comp[of _ \<Gamma>])
    subgoal using phi.particular_struct_morphism_axioms by blast      
    by (simp add: phi1_auto.particular_struct_morphism_axioms)
  then have D: \<open>(\<phi>' \<circ> \<phi>) \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close> by blast

  show \<open>y\<^sub>1 = \<phi>' y\<^sub>1\<close> 
    if A: 
      \<open>\<phi>' y\<^sub>1 \<in> \<P>\<close> 
      \<open>y \<in> particulars \<Gamma>\<^sub>x\<close>
      \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ;
               \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = \<phi>' y\<^sub>1 \<longleftrightarrow> z = y\<close>
      \<open>y\<^sub>1 \<in> \<P>\<close>
  proof -
    obtain B: \<open>y \<in> phi.src.endurants\<close> using A(2) by simp
    have C: \<open>\<phi> y = \<phi>' y\<^sub>1\<close>
      using A(3)[OF B phi_in_morphs] by simp 
    have E: \<open>\<phi>' (\<phi> y) = \<phi>' y\<^sub>1\<close> using A(3)[OF B D] by simp
    have F: \<open>\<phi> y \<in> \<P>\<close>  by (simp add: C A(1))
    obtain \<sigma> where \<open>particular_struct_endomorphism \<Gamma> \<sigma>\<close>
                   and sigma[simp]: \<open>\<sigma> (\<phi> y) = y\<^sub>1\<close>
      using phi1.choice[simplified,of \<open>\<phi> y\<close> y\<^sub>1,OF F A(4) E] 
      by metis
    then interpret sigma_auto: particular_struct_endomorphism \<Gamma> \<sigma> 
      by simp
    interpret sigma: particular_struct_morphism \<Gamma> \<Gamma> \<sigma> 
      using sigma_auto.particular_struct_morphism_axioms by simp
    interpret sigma_phi: particular_struct_morphism \<Gamma>\<^sub>x \<Gamma> \<open>\<sigma> \<circ> \<phi>\<close>
      apply (intro particular_struct_morphism_comp[of _ \<Gamma>])
      subgoal using phi.particular_struct_morphism_axioms 
        by blast      
      by (simp add: sigma.particular_struct_morphism_axioms)
    have G: \<open>(\<sigma> \<circ> \<phi>) \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>
      using sigma_phi.particular_struct_morphism_axioms
      by blast
    show ?thesis
      using A(3)[OF B G,simplified] by simp
  qed
  show \<open>\<phi>' x = x\<close>
    if A:
      \<open>x \<in> \<P>\<close> 
      \<open>y \<in> particulars \<Gamma>\<^sub>x\<close>
      \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ;
                 \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
  proof -
    obtain B: \<open>y \<in> phi.src.endurants\<close> using A(2) by simp
    have C: \<open>\<phi> y = x\<close> using A(3)[OF B phi_in_morphs] by simp
    then show \<open>\<phi>' x = x\<close> using A(3)[OF B D] by simp
  qed
qed

theorem  anchored_are_the_non_permutable: \<open>\<P>\<^sub>\<down> = \<P>\<^sub>1\<^sub>!\<close>  
  using anchored_are_non_permutable non_permutable_are_anchored 
  by blast

end

end
