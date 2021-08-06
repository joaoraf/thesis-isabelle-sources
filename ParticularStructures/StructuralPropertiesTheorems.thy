subsection \<open>Permutability and Isomorphical Uniqueness\<close>

theory StructuralPropertiesTheorems
  imports IsomorphicalUniqueness Permutability CollapsibleParticulars
begin

context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>It turns out that the set of isomorphically unique particulars of a particular
  structure is identical to the set of non-permutable particulars, as shown in the 
  following theorem and lemmas:\<close>

lemma im_unique_particulars_are_non_permutable_particulars: 
    \<open>\<P>\<^sub>\<simeq>\<^sub>! \<subseteq> \<P>\<^sub>1\<^sub>!\<close>
proof (intro subsetI ballI ; clarsimp simp: isomorphically_unique_particulars_def)
  fix x \<phi> y
  assume as1: \<open>particular_struct_endomorphism \<Gamma> \<phi>\<close> \<open>x \<in> \<E>\<close>
      \<open>\<forall>\<phi>\<in>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>. \<forall>\<sigma>\<in>Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>.\<forall>y\<in>\<E>. (\<sigma> y = \<phi> x) = (y = x)\<close>
      \<open>y \<in> \<E>\<close>
  interpret I: particular_struct_endomorphism \<open>\<Gamma>\<close> \<open>\<phi>\<close> using as1(1) by blast
  have A: \<open>\<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close> if \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> \<open>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> for \<phi> \<sigma> y
    using that as1(3) by metis
  obtain \<pi> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>inj \<pi>\<close>
    using injection_to_ZF_exist by blast
  have pi_isomorph: \<open>\<pi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    using  \<open>inj \<pi>\<close> by (meson UNIV_I inj_morph_img_BijMorphs inj_on_id inj_on_subset subsetI)
  have pi_sigma_morph: \<open>\<pi> \<circ> \<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<pi> \<Gamma>\<^esub>\<close>
    by (meson I.particular_struct_morphism_axioms bijections1_are_morphisms morphisms_are_closed_under_comp morphs_I pi_isomorph)
  have \<open>\<pi> x = \<pi> (\<phi> x)\<close>
    using A[of \<open>\<pi>\<close> \<open>\<pi> \<circ> \<phi>\<close>, OF pi_isomorph pi_sigma_morph \<open>x \<in> \<E>\<close>,simplified]
    by simp
  then have \<open>x = \<phi> x\<close>
    by (rule \<open>inj \<pi>\<close>[THEN inj_onD]; simp)
  then show \<open>\<phi> y = x \<longleftrightarrow> y = x\<close>
    apply (intro iffI ; simp)    
    by (rule A[where y=y and \<phi> = \<pi> and \<sigma> = \<open>\<pi> \<circ> \<phi>\<close>,OF _ _ \<open>y \<in> \<E>\<close>,simplified o_apply
          , THEN iffD1] ; (intro pi_sigma_morph pi_isomorph)? ; simp)      
qed

lemma non_permutable_particulars_are_im_unique_particulars: 
  \<open>\<P>\<^sub>1\<^sub>! \<subseteq> \<P>\<^sub>\<simeq>\<^sub>!\<close>
proof (intro subsetI ballI ; clarsimp simp: isomorphically_unique_particulars_def)
  fix x y :: \<open>'p\<close> and \<phi> \<sigma> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close> and f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close>
  assume as: 
      \<open>particular_struct_morphism \<Gamma> (MorphImg \<phi> \<Gamma>) \<sigma>\<close>       
      \<open>\<forall>\<phi>\<in>EndoMorphs\<^bsub>\<Gamma>\<^esub>. \<forall>y\<in>\<E>. \<phi> y = x \<longleftrightarrow> y = x\<close> 
      \<open>inj_on \<phi> \<E>\<close> 
      \<open>inj f\<close>     
      \<open>x \<in> \<E>\<close>
      \<open>y \<in> \<E>\<close>
  have A: \<open>\<phi> y = x \<longleftrightarrow> y = x\<close> if \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> for \<phi> y using as(2) that by blast  
  interpret I1: particular_struct_morphism \<open>\<Gamma>\<close> \<open>MorphImg \<phi> \<Gamma>\<close> \<open>\<sigma>\<close> using as(1) by simp
  interpret I: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
    using as(3,4) inj_morph_img_isomorphism[of \<open>\<phi>\<close>] by blast
  interpret Inv: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<open>I.inv_morph\<close>    
    using particular_struct_bijection_iff_particular_struct_bijection_1 by blast

  have B: \<open>particular_struct_morphism \<Gamma> \<Gamma> (I.inv_morph \<circ> \<sigma>)\<close>
    apply (intro particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> \<Gamma>\<close>])
    subgoal using I1.particular_struct_morphism_axioms by blast
    by (simp add: particular_struct_bijection.axioms(1) particular_struct_injection.axioms(1))

  have C: \<open>I.inv_morph \<circ> \<sigma> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
    apply (simp)
    apply (intro_locales) 
   using B particular_struct_morphism_def 
      pre_particular_struct_morphism_def by blast+

  have D: \<open>I.inv_morph (\<sigma> x) = x\<close> using A[OF C \<open>x \<in> \<E>\<close>,simplified] .
  have E: \<open>I.inv_morph (\<phi> x) = x\<close> using \<open>x \<in> \<E>\<close> by simp
  have F: \<open>I.inv_morph (\<sigma> x) = I.inv_morph (\<phi> x)\<close> using D E by simp
  show \<open>\<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>
    apply (intro iffI ; simp?)
    subgoal
      apply (rule A[where y=y and \<phi> = \<open>I.inv_morph \<circ> \<sigma>\<close>,OF C \<open>y \<in> \<E>\<close>,THEN iffD1])
      by (simp add: E)
    subgoal
      apply (rule F inj_onD[OF Inv.morph_is_injective,simplified,OF F])
      subgoal using \<open>x \<in> \<E>\<close> by (simp add: I1.morph_preserves_particulars)
      using \<open>x \<in> \<E>\<close> by (simp add: I.morph_preserves_particulars)
    done 
qed

theorem non_permutable_particulars_are_the_unique_particulars: 
    \<open>\<P>\<^sub>1\<^sub>! = \<P>\<^sub>\<simeq>\<^sub>!\<close>
  using im_unique_particulars_are_non_permutable_particulars
     non_permutable_particulars_are_im_unique_particulars by simp    


text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of non-permutable particulars is a subset of the set of
  non-collapsible particulars, although the converse does not
  hold, in general:
\<close>

theorem  non_permutables_are_non_collapsible: \<open>\<P>\<^sub>1\<^sub>! \<subseteq> \<P>\<^sub>n\<^sub>c\<close> 
proof (intro subsetI ; elim non_permutables_E ; 
        intro nonCollapsibleParticularsI notI ;
        (elim collapsibleE)? ; assumption?
        ; rename_tac x\<^sub>1 \<phi> x\<^sub>2)
  fix x\<^sub>1 x\<^sub>2 \<phi>
  assume A: \<open>x\<^sub>1 \<in> \<E>\<close> \<open>x\<^sub>2 \<in> \<E>\<close> \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> \<open>\<phi> x\<^sub>1 = \<phi> x\<^sub>2\<close>            
    and B: \<open>non_permutable x\<^sub>1\<close> \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>   
  note A(1,2)[simp,intro!]
  note A1[simp] = A(3)[simplified A(4)] A(4)
  interpret phi: particular_struct_endomorphism \<Gamma> \<phi> using B(2) by simp
  note C1 = B(1)[THEN non_permutable_E,OF B(2) \<open>x\<^sub>2 \<in> \<E>\<close>] and
       C2 = B(1)[THEN non_permutable_E,OF B(2) \<open>x\<^sub>1 \<in> \<E>\<close>]
  have D[simp]: \<open>\<phi> x\<^sub>1 = x\<^sub>1\<close> using C2 by simp     
  show False    
    using A1(1) A1(2) C1 D by presburger
qed


end

end