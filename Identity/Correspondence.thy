text_raw \<open>\subsection[Correspondence Function]{Correspondence Function\isalabel{sec:correspondence-function}}\<close>

theory Correspondence
  imports IdentifiabilityAndIsomorphicalUniqueness "../ParticularStructures/StructuralPropertiesTheorems"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We can leverage the ability of an identifying predicate to pick up
  a particular of a particular structure in any isomorphic structure
  to construct a representation-independent notion of the ``identity
  of the particular''. We achieve that by using the 
  \emph{correspondence function} (\<open>\<pi>\<close>), which, for any particular
  structures \<open>\<Gamma>\<^sub>1\<close> and \<open>\<Gamma>\<^sub>2\<close>, and any particular \<open>x\<close> of \<open>\<Gamma>\<^sub>1\<close>, gives 
  the element \<open>y\<close> of \<open>\<Gamma>\<^sub>2\<close> that is uniquely mapped by any \<open>\<Gamma>\<^sub>1\<close>-\<open>\<Gamma>\<^sub>2\<close>
  isomorphism (assuming \<open>x\<close> is isomorphically unique).
\<close>
text_raw \<open>\par\<close>
locale isomorphic_pair_of_particular_structures_sig =
    src: particular_struct_defs where \<Gamma> = \<open>\<Gamma>\<^sub>1\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    tgt: particular_struct_defs where \<Gamma> = \<open>\<Gamma>\<^sub>2\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>
  for \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
      \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close> 
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In fact, the way we define \<open>\<pi>\<close> is by choosing any bijection between
  \<open>\<Gamma>\<^sub>1\<close> e \<open>\<Gamma>\<^sub>2\<close> and using it to identity the particular that corresponds
  to \<open>x\<close> in \<open>\<Gamma>\<^sub>2\<close>, since \<open>x\<close> is isomorphically invariant:
\<close>
text_raw \<open>\par\<close>
definition \<pi> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> where
  \<open>\<pi> \<equiv> SOME \<sigma>. particular_struct_bijection_1 \<Gamma>\<^sub>1 \<sigma> \<and> \<Gamma>\<^sub>2 = MorphImg \<sigma> \<Gamma>\<^sub>1\<close>

end

context particular_struct
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Similarly, we can define, for any isomorphically unique particular
  \<open>x\<close> of \<open>\<Gamma>\<close>, a function that, given any particular structure \<open>\<Gamma>'\<close>
  isomorphic to \<open>\<Gamma>\<close>, identifies the correspondent of \<open>x\<close> in it. 
  We call this function \<open>\<Gamma>_corresp\<close> and define it formally as:
\<close> 
text_raw \<open>\par\<close>
definition \<Gamma>_corresp :: \<open>'p \<Rightarrow> ('p\<^sub>1,'q) particular_struct \<Rightarrow> 'p\<^sub>1\<close> where
 \<open>\<Gamma>_corresp x \<Gamma>' \<equiv> 
      let \<phi> = (SOME \<sigma>. particular_struct_bijection_1 \<Gamma> \<sigma> \<and> \<Gamma>' = MorphImg \<sigma> \<Gamma>)
      in \<phi> x \<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Now, given some \<open>x\<close> in \<open>\<Gamma>\<^sub>1\<close>, \<open>\<Gamma>_corresp x\<close> is a function from
  particular structures (of any particular type) to particulars
  of that structure. This function represents the identity of \<open>x\<close>
  in all particular structures isomorphic to \<open>\<Gamma>\<close>, independent of
  the specific representation of the particulars in them. 

  We propose that this function, \<open>\<Gamma>_corresp x\<close>, is a good 
  structurally-invariant representation of the identity of \<open>x\<close>.
\<close>
text_raw \<open>\par\<close>
end


locale isomorphic_pair_of_particular_structures =
    isomorphic_pair_of_particular_structures_sig 
    where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<^sub>1\<close> and \<Gamma>\<^sub>2 = \<open>\<Gamma>\<^sub>2\<close> and 
      Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    src: particular_struct where \<Gamma> = \<open>\<Gamma>\<^sub>1\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    tgt: particular_struct where \<Gamma> = \<open>\<Gamma>\<^sub>2\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>
  for \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
      \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close> +
  assumes
    structs_are_isomorphic: 
    \<open>\<exists>\<sigma>. particular_struct_bijection_1 \<Gamma>\<^sub>1 \<sigma> \<and> \<Gamma>\<^sub>2 = MorphImg \<sigma> \<Gamma>\<^sub>1\<close>
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> pi_isomorphism: \<open>particular_struct_bijection_1 \<Gamma>\<^sub>1 \<pi>\<close> 
  and Gamma2_eq: \<open>\<Gamma>\<^sub>2 = MorphImg \<pi> \<Gamma>\<^sub>1\<close>
  using someI_ex[OF structs_are_isomorphic, simplified \<pi>_def[symmetric]]
  by auto

end

notation \<^marker>\<open>tag aponly\<close> isomorphic_pair_of_particular_structures (infix \<open>\<simeq>\<^sub>i\<close> 75)

lemma \<^marker>\<open>tag (proof) aponly\<close>  isomorphic_pair_of_particular_structures_refl[intro]:
  assumes \<open>particular_struct \<Gamma>\<close>
  shows \<open>\<Gamma> \<simeq>\<^sub>i \<Gamma>\<close>
  apply (simp add: isomorphic_pair_of_particular_structures_def assms)
  apply unfold_locales
  apply (intro exI[of _ \<open>id\<close>] ; simp)
  by (metis assms particular_struct_def particular_struct_eqI 
      ufo_particular_theory.id_is_isomorphism ufo_particular_theory_sig.\<Gamma>_simps)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_pair_of_particular_structures_sym[sym]:
  assumes \<open>\<Gamma>\<^sub>1 \<simeq>\<^sub>i \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma>\<^sub>2 \<simeq>\<^sub>i \<Gamma>\<^sub>1\<close>
proof -
  interpret isomorphic_pair_of_particular_structures \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close>
    using assms .
  
  interpret pi: particular_struct_bijection_1 \<open>\<Gamma>\<^sub>1\<close> \<open>\<pi>\<close>
    using pi_isomorphism .  

  show \<open>?thesis\<close>
    apply (intro_locales)
    apply (unfold_locales)
    apply (intro exI[of _ \<open>pi.inv_morph\<close>] conjI )
    subgoal using Gamma2_eq particular_struct_bijection_iff_particular_struct_bijection_1 pi.inv_is_bijective_morphism by auto
    by (metis Gamma2_eq particular_struct_bijection_iff_particular_struct_bijection_1 
              pi.inv_is_bijective_morphism)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_pair_of_particular_structures_trans[trans]:
  assumes \<open>\<Gamma>\<^sub>1 \<simeq>\<^sub>i \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<simeq>\<^sub>i \<Gamma>\<^sub>3\<close>
  shows \<open>\<Gamma>\<^sub>1 \<simeq>\<^sub>i \<Gamma>\<^sub>3\<close>
proof -
  interpret P12: isomorphic_pair_of_particular_structures \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close>
    using assms(1) .
  interpret pi12: particular_struct_bijection_1 \<open>\<Gamma>\<^sub>1\<close> \<open>P12.\<pi>\<close>
    using P12.pi_isomorphism .
  interpret P23: isomorphic_pair_of_particular_structures \<open>\<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>3\<close>
    using assms(2) .
  interpret pi23: particular_struct_bijection_1 \<open>\<Gamma>\<^sub>2\<close> \<open>P23.\<pi>\<close>
    using P23.pi_isomorphism .
  have A: \<open>\<Gamma>\<^sub>3 = MorphImg P23.\<pi> (MorphImg P12.\<pi> \<Gamma>\<^sub>1)\<close>    
    using P12.Gamma2_eq P23.Gamma2_eq by auto
  interpret P13: particular_struct_bijection_1 \<open>\<Gamma>\<^sub>1\<close> \<open>P23.\<pi> \<circ> P12.\<pi>\<close>
    apply (rule particular_struct_bijection_1_comp)
    subgoal using pi12.particular_struct_bijection_1_axioms by auto
    subgoal using P12.Gamma2_eq pi23.particular_struct_bijection_1_axioms by auto
    done
      
  show \<open>?thesis\<close>
    apply (unfold_locales)
    apply (intro exI[of _ \<open>P23.\<pi> \<circ> P12.\<pi>\<close>] conjI P13.particular_struct_bijection_1_axioms  
              ; (simp)?)
    using A by metis
qed
    

context ufo_particular_theory_sig
begin

definition \<^marker>\<open>tag aponly\<close> correspondentIn :: \<open>'p \<Rightarrow> ('p\<^sub>1,'q) particular_struct \<Rightarrow> 'p\<^sub>1\<close>  
  where \<open>correspondentIn x \<Gamma>' \<equiv> 
  THE y. \<forall>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>. \<forall>z \<in> particulars \<Gamma>. \<sigma> z = y \<longleftrightarrow> z = x\<close>

end

context particular_struct_bijection_1
begin

lemma \<^marker>\<open>tag (proof) aponly\<close>
  assumes  \<open>x \<in> src.identifiables\<close> 
          \<open>\<phi>\<^sub>1 \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>\<close>
           \<open>e \<in> src.\<P>\<close>
  shows \<open>\<phi>\<^sub>1 e = src.correspondentIn x (MorphImg \<phi> src.\<Gamma>) \<longleftrightarrow> e = x\<close>
proof -
  have np_x: \<open>src.non_permutable x\<close> 
    using assms(1) src.identifiables_are_the_non_permutables
    by auto
  note np_x_E = src.non_permutable_E[OF np_x]
  interpret phi1: particular_struct_morphism \<open>src.\<Gamma>\<close> \<open>MorphImg \<phi> src.\<Gamma>\<close> \<phi>\<^sub>1
    using assms by blast
  have phi1_tgt: \<open>phi1.tgt.endurants = tgt.endurants\<close>        
      using tgt.\<Gamma>_simps(2) tgt_Gamma_eq_Morph_img by auto
  obtain P where P: \<open>x \<in> src.\<P>\<close> \<open>identity_pred src.\<Gamma> P x\<close>
    using assms(1) by blast
  obtain \<omega>\<^sub>1 :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close> where \<omega>\<^sub>1: \<open>inj \<omega>\<^sub>1\<close> using src.injection_to_ZF_exist by blast
  obtain \<omega>\<^sub>2 :: \<open>'p\<^sub>2 \<Rightarrow> ZF\<close> where \<omega>\<^sub>2: \<open>inj \<omega>\<^sub>2\<close> using tgt.injection_to_ZF_exist by blast
  have A: \<open>\<omega>\<^sub>1 \<in> BijMorphs1\<^bsub>src.\<Gamma>,TYPE(ZF)\<^esub>\<close>
    apply (simp ; safe)
    subgoal using \<omega>\<^sub>1 inj_on_subset by auto
    using inj_on_id by blast
  have tgt_G: \<open>tgt.\<Gamma> = MorphImg \<phi> src.\<Gamma>\<close> 
    using tgt_Gamma_eq_Morph_img by blast

  interpret omega1: particular_struct_bijection_1 \<open>src.\<Gamma>\<close> \<omega>\<^sub>1 \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE(ZF)\<close>
    apply (intro src.inj_morph_img_isomorphism)
    subgoal using \<omega>\<^sub>1 inj_on_subset by auto
    using inj_on_id by blast

  interpret omega2: particular_struct_bijection_1 \<open>MorphImg \<phi> src.\<Gamma>\<close> \<omega>\<^sub>2 \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE(ZF)\<close>
    apply (intro tgt.inj_morph_img_isomorphism[simplified tgt_G])
    subgoal using \<omega>\<^sub>2 inj_on_subset by blast
    using inj_on_id by blast

  obtain Pi: \<open>\<And>\<Gamma>' \<phi> y. \<Gamma>' \<in> IsoModels\<^bsub>src.\<Gamma>,TYPE(ZF)\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>src.\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> P \<Gamma>' y = (\<forall>z\<in>phi1.src.endurants. (y = \<phi> z) = (z = x))\<close>
    using P(2)[THEN identity_pred_E] by metis
  have B: \<open>\<omega>\<^sub>1 \<circ> \<phi>\<inverse> \<circ> \<phi>\<^sub>1 \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<omega>\<^sub>1 src.\<Gamma>\<^esub>\<close>
    apply (intro morphs_I 
        particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> src.\<Gamma>\<close>] 
        particular_struct_morphism_comp[of _ \<open>src.\<Gamma>\<close>])
    subgoal using assms(2) by blast
    subgoal 
      by (metis particular_struct_eqI particular_struct_bijection.inv_is_bijective_morphism 
            particular_struct_bijection_1_axioms 
            particular_struct_bijection_def 
            particular_struct_bijection_iff_particular_struct_bijection_1 
            particular_struct_injection_def ufo_particular_theory_sig.\<Gamma>_simps) 
    using A particular_struct_bijection_1_def particular_struct_injection_def by blast

  have COND2: \<open>MorphImg \<omega>\<^sub>1 src.\<Gamma> \<in> IsoModels\<^bsub>src.\<Gamma>,TYPE(ZF)\<^esub>\<close>    
    using A by blast
  have COND3: \<open>\<omega>\<^sub>1 \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<omega>\<^sub>1 src.\<Gamma>\<^esub>\<close>        
    using omega1.particular_struct_morphism_axioms by blast
  have COND4: \<open>\<forall>z\<in>src.\<P>. (\<omega>\<^sub>1 x = \<omega>\<^sub>1 z) = (z = x)\<close> 
    using \<omega>\<^sub>1[THEN injD] by auto
  note R1 = Pi[of \<open>MorphImg \<omega>\<^sub>1 src.\<Gamma>\<close> _ \<open>\<omega>\<^sub>1 x\<close>,OF COND2]
  have P_1: \<open>P (MorphImg \<omega>\<^sub>1 src.\<Gamma>) (\<omega>\<^sub>1 x)\<close>
    using R1[of \<omega>\<^sub>1,OF COND3,simplified] COND4 by auto
  have P_2: \<open>\<omega>\<^sub>1 x = \<phi>' z \<longleftrightarrow> z = x\<close> if
    \<open>\<phi>' \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<omega>\<^sub>1 src.\<Gamma>\<^esub>\<close>
    \<open>z \<in> src.\<P>\<close> for \<phi>' z
    using that Pi[of \<open>MorphImg \<omega>\<^sub>1 src.\<Gamma>\<close> _ \<open>\<omega>\<^sub>1 x\<close>,simplified P_1 simp_thms,
        rule_format,OF COND2] by auto
  have P_3: \<open>x = \<phi>\<inverse> (\<phi>\<^sub>1 z) \<longleftrightarrow> z = x\<close> if AA: \<open>z \<in> src.\<P>\<close> for z
    using P_2[OF B,simplified,OF AA] injD[OF \<omega>\<^sub>1] by auto

  interpret phi_inv: particular_struct_bijection_1 \<open>MorphImg \<phi> src.\<Gamma>\<close> \<open>\<phi>\<inverse>\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (simp  only: tgt.isomorphism_1_iff_inj[simplified tgt_G] ; intro conjI)
    subgoal by simp    
    using \<omega>\<^sub>1 by blast      

  have phi_inv_img_phi_img[simp]: \<open>MorphImg \<phi>\<inverse> (MorphImg \<phi> src.\<Gamma>) = src.\<Gamma>\<close>
    by (metis inv_is_bijective_morphism particular_struct_eqI particular_struct_bijection_iff_particular_struct_bijection_1 src.\<Gamma>_simps)

  interpret phi_inv_phi: particular_struct_morphism src.\<Gamma> src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<phi>\<^sub>1\<close> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>
    by (intro  particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> src.\<Gamma>\<close>]
        phi1.particular_struct_morphism_axioms
        phi_inv.particular_struct_morphism_axioms[simplified phi_inv_img_phi_img])
  
  interpret phi_inv_phi_auto: particular_struct_endomorphism src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<phi>\<^sub>1\<close>
    by (intro_locales)
  
  note ident_pred_I = src.identity_respects_isomorphisms[OF P(2),simplified tgt_G]
  have phi_inv_phi_auto_endurants[simp]: \<open>phi_inv_phi_auto.endurants = src.\<P>\<close>
    by auto
  let ?guess = \<open>\<phi>\<^sub>1 x\<close>
  have case1: \<open>\<sigma> z = ?guess \<longleftrightarrow> z = x\<close> 
    if as: \<open>\<sigma> \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>\<close> \<open>z \<in> omega1.src.endurants\<close>    
    for \<sigma> z
  proof -
    interpret sigma: particular_struct_morphism src.\<Gamma> \<open>MorphImg \<phi> src.\<Gamma>\<close> \<sigma>
      using as(1) by blast
    note AA = as(2)[simplified phi_inv_phi_auto_endurants]

    interpret phi_inv_sigma: particular_struct_morphism src.\<Gamma> src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<sigma>\<close> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>
      by (intro particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> src.\<Gamma>\<close>]
                sigma.particular_struct_morphism_axioms
                phi_inv.particular_struct_morphism_axioms[simplified phi_inv_img_phi_img])
    interpret phi_inv_sigma_auto: particular_struct_endomorphism src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<sigma>\<close> 
      by (intro_locales)
    have phi_inv_sigma_in_auto: \<open>\<phi>\<inverse> \<circ> \<sigma> \<in> EndoMorphs\<^bsub>src.\<Gamma>\<^esub>\<close>
      using phi_inv_sigma_auto.particular_struct_endomorphism_axioms by blast

    have x_const_phi1[simp]: \<open>\<phi>\<inverse> (\<phi>\<^sub>1 x) = x\<close> using P_3[OF \<open>x \<in> src.\<P>\<close>] by simp
    have x_const_sigma[simp]: \<open>\<phi>\<inverse> (\<sigma> x) = x\<close> using np_x_E[OF phi_inv_sigma_in_auto,simplified,OF \<open>x \<in> src.\<P>\<close>] by simp
    have omega2_src_end[simp]: \<open>omega2.src.endurants = tgt.\<P>\<close>      
      using phi1_tgt by blast 
    obtain DD: \<open>\<phi>\<^sub>1 z \<in> tgt.endurants\<close> \<open>\<sigma> z \<in> tgt.endurants\<close>
      using \<open>z \<in> src.\<P>\<close> 
      using phi1.morph_preserves_particulars phi1_tgt sigma.morph_preserves_particulars by auto
    have BB[simp]: \<open>\<phi>\<^sub>1 x = \<sigma> x\<close>
      using x_const_phi1 x_const_sigma
          phi_inv.morph_is_injective[simplified omega2_src_end,THEN inj_onD
              , OF _ DD]
      by (metis I_img_eq_tgt_I P(1) morph_inv_morph_img phi1.morph_preserves_particulars sigma.morph_preserves_particulars src.\<Gamma>_simps(2) tgt.\<Gamma>_simps(2) tgt_Gamma_eq_Morph_img)
           
    have EE: \<open>\<phi>\<inverse> (\<phi>\<^sub>1 z) = \<phi>\<inverse> (\<sigma> z) \<longleftrightarrow> \<sigma> z = \<phi>\<^sub>1 z\<close>
      using inv_morph_injective[THEN inj_onD,OF _ DD] by auto
    note ident_pred_I[of \<phi>,
            THEN identity_pred_E]
    show ?thesis
      apply simp       
      using AA np_x_E phi_inv_sigma_in_auto by force
  qed
  have case2: \<open>\<exists>!y. \<forall>\<sigma>\<in>Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>.
            \<forall>z\<in>omega1.src.endurants. (\<sigma> z = y) = (z = x)\<close>
  proof (intro ex1I[of _ \<open>?guess\<close>] , metis case1)
    fix y
    assume  
        \<open>\<forall>\<sigma> \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>.
         \<forall>z\<in>omega1.src.endurants. \<sigma> z = y \<longleftrightarrow> z = x\<close>
    then have as: \<open>\<sigma> z = y \<longleftrightarrow> z = x\<close> 
      if \<open>\<sigma> \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>\<close>
         \<open>z \<in> src.\<P>\<close> for \<sigma> z
      using that 
      by simp

    show \<open>y = \<phi>\<^sub>1 x\<close>    
      by (rule as[of \<phi>\<^sub>1 x,THEN iffD2,symmetric] ;
            (intro \<open>x \<in> src.\<P>\<close> assms(2))? ; simp)
  qed

  have case3: \<open>\<sigma> z = \<phi> x \<longleftrightarrow> z = x\<close> 
    if as: \<open>\<sigma> \<in> Morphs\<^bsub>src.\<Gamma>,MorphImg \<phi> src.\<Gamma>\<^esub>\<close> \<open>z \<in> omega1.src.endurants\<close>    
    for \<sigma> z
  proof -
    interpret sigma: particular_struct_morphism src.\<Gamma> \<open>MorphImg \<phi> src.\<Gamma>\<close> \<sigma>
      using as(1) by blast
    note AA = as(2)[simplified phi_inv_phi_auto_endurants]

    interpret phi_inv_sigma: particular_struct_morphism src.\<Gamma> src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<sigma>\<close> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>
      by (intro particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> src.\<Gamma>\<close>]
                sigma.particular_struct_morphism_axioms
                phi_inv.particular_struct_morphism_axioms[simplified phi_inv_img_phi_img])
    interpret phi_inv_sigma_auto: particular_struct_endomorphism src.\<Gamma> \<open>\<phi>\<inverse> \<circ> \<sigma>\<close> 
      by (intro_locales)
    have phi_inv_sigma_in_auto: \<open>\<phi>\<inverse> \<circ> \<sigma> \<in> EndoMorphs\<^bsub>src.\<Gamma>\<^esub>\<close>
      using phi_inv_sigma_auto.particular_struct_endomorphism_axioms by blast

    have COND3: \<open>particular_struct_morphism src.\<Gamma> (MorphImg \<omega>\<^sub>1 src.\<Gamma>) (\<omega>\<^sub>1 \<circ> \<phi>\<inverse> \<circ> \<phi>)\<close>
      apply (intro 
            particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> src.\<Gamma>\<close>]
            particular_struct_morphism_comp[of _ \<open>src.\<Gamma>\<close>])
      subgoal using particular_struct_bijection_1.phi_in_iso_morphs particular_struct_bijection_1_axioms particular_struct_bijection_1_def particular_struct_injection_def by blast
      subgoal using phi_inv.particular_struct_morphism_axioms by auto      
      by (simp add: omega1.particular_struct_morphism_axioms)
    
    have P_4: \<open>x = \<phi>\<inverse> (\<phi> z) \<longleftrightarrow> z = x\<close> if AA: \<open>z \<in> src.\<P>\<close> for z
      using inv_into_f_f[OF morph_is_injective,simplified inv_morph_def[symmetric]
          , OF AA] by metis

    have x_const_phi1[simp]: \<open>\<phi>\<inverse> (\<phi> x) = x\<close> using P_4[OF \<open>x \<in> src.\<P>\<close>] by simp
    have x_const_sigma[simp]: \<open>\<phi>\<inverse> (\<sigma> x) = x\<close> using np_x_E[OF phi_inv_sigma_in_auto,simplified,OF \<open>x \<in> src.\<P>\<close>] by simp
    have omega2_src_end[simp]: \<open>omega2.src.endurants = tgt.\<P>\<close>      
      using phi1_tgt by blast 
    obtain DD: \<open>\<phi>\<^sub>1 z \<in> tgt.endurants\<close> \<open>\<sigma> z \<in> tgt.endurants\<close>
      using \<open>z \<in> src.\<P>\<close> 
      using phi1.morph_preserves_particulars phi1_tgt sigma.morph_preserves_particulars by auto
    have BB[simp]: \<open>\<phi> x = \<sigma> x\<close>
      using x_const_sigma          
      by (metis I_img_eq_tgt_I P(1) morph_inv_morph_img sigma.morph_preserves_particulars src.\<Gamma>_simps(2) tgt.\<Gamma>_simps(2) tgt_Gamma_eq_Morph_img)
               
    show ?thesis
      apply simp             
      by (metis P(1) case2 src.\<Gamma>_simps(2) that)
  qed

  have corresp_x_eq_phi_x: \<open>src.correspondentIn x (MorphImg \<phi> src.\<Gamma>) = \<phi> x\<close>
    apply (simp only: src.correspondentIn_def)
    apply (intro the1_equality case2)
    apply (intro ballI)
    by (intro case3 ; simp)

  show \<open>?thesis\<close>    
    apply (intro iffI ; simp?)
    subgoal
      apply (simp add: corresp_x_eq_phi_x)      
      using assms(2) assms(3) case3 by auto      
    by (simp only: src.correspondentIn_def
        ; intro the1_equality[symmetric] case2
        ; clarify ; intro case1 ; simp)        
qed

end

end

