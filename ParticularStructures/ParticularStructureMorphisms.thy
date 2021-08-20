text_raw \<open>\section[Particular Structures Homomorphisms]{Particular Structures Homomorphisms\isalabel{sec:particular-structure-morphisms}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section we show how certain functions between sets of 
  particulars of two particular structures give rise to a 
  notion of homorphisms between these structures. We call
  such functions \emph{particular structure homomorphisms} or
  simply \emph{particular structure morphisms}.    
\<close>

subsection \<open>Definitions\<close>

theory \<^marker>\<open>tag aponly\<close> ParticularStructureMorphisms
 imports ParticularStructure "../Misc/WellfoundedExtra" "HOL-Library.FuncSet" "../Misc/FuncSetExtra"
begin \<^marker>\<open>tag aponly\<close>

no_notation \<^marker>\<open>tag aponly\<close> converse (\<open>(_\<inverse>)\<close> [1000] 999)

locale \<^marker>\<open>tag aponly\<close> ufo_src_tgt_particular_models_sig =  
    src: particular_struct_defs 
    where \<Gamma> = \<open>\<Gamma>\<^sub>1\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>1\<close> 
      and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  + 
    tgt: particular_struct_defs 
    where \<Gamma> = \<open>\<Gamma>\<^sub>2\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>2\<close> 
      and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  
  for     
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and    
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 

text \<^marker>\<open>tag bodyonly\<close> \<open>
 Let's start with two particular structures, @{term_type \<Gamma>\<^sub>1} and
 @{term_type \<Gamma>\<^sub>2}, where @{typ \<open>'p\<^sub>1\<close>} and @{typ \<open>'p\<^sub>2\<close>} denote two types
 of particulars and @{typ \<open>'q\<close>} denotes a type of qualia. We call 
 \<open>\<Gamma>\<^sub>1\<close> the \emph{source structure} and \<open>\<Gamma>\<^sub>2\<close> the \emph{target structure}.
 In this context, for the purpose of simplifying the theories presented 
 in this section, we define the following abbreviations:
\<close>

context \<^marker>\<open>tag aponly\<close> ufo_src_tgt_particular_models_sig
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The infix symbols \<open>(\<triangleleft>\<^sub>s)\<close> and \<open>(\<triangleleft>\<^sub>t)\<close> denote, respectively, the \emph{inherence}
  relations of the source and target structures:\<close>

abbreviation src_inheres_in (infix \<open>\<triangleleft>\<^sub>s\<close> 75) where
  \<open>x \<triangleleft>\<^sub>s y \<equiv> src.inheresIn x y\<close>

abbreviation tgt_inheres_in (infix \<open>\<triangleleft>\<^sub>t\<close> 75) where
  \<open>x \<triangleleft>\<^sub>t y \<equiv> tgt.inheresIn x y\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The infix symbols \<open>(\<leadsto>\<^sub>s)\<close> and \<open>(\<leadsto>\<^sub>t)\<close> denote, respectively, the 
  \emph{quale association} relations of the source and target structures:\<close>

abbreviation src_assoc_quale (infix \<open>\<leadsto>\<^sub>s\<close> 75) where
  \<open>x \<leadsto>\<^sub>s y \<equiv> src.assoc_quale x y\<close>

abbreviation tgt_assoc_quale (infix \<open>\<leadsto>\<^sub>t\<close> 75) where
  \<open>x \<leadsto>\<^sub>t y \<equiv> tgt.assoc_quale x y\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The infix symbols \<open>(\<longlonglongrightarrow>\<^sub>s)\<close> and \<open>(\<longlonglongrightarrow>\<^sub>t)\<close> denote, respectively, the \emph{towards} 
  relations of the source and target structures:\<close>

abbreviation src_towards (infix \<open>\<longlongrightarrow>\<^sub>s\<close> 75) where
  \<open>x \<longlongrightarrow>\<^sub>s y \<equiv> src.towards x  y\<close>

abbreviation tgt_towards (infix \<open>\<longlongrightarrow>\<^sub>t\<close> 75) where
  \<open>x \<longlongrightarrow>\<^sub>t y \<equiv> tgt.towards x  y\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The symbols \<open>\<Q>\<^sub>s\<close> and \<open>\<Q>\<^sub>t\<close> denote, respectively, the sets of qualia
  of the source and target structures:\<close>

abbreviation \<open>\<Q>\<^sub>s \<equiv> src.qualia\<close>

abbreviation \<open>\<Q>\<^sub>t \<equiv> tgt.qualia\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 For any symbol \<open>S\<close> defined in the context of a particular structure
 or in the context of a particular theory,
 i.e. those defined in the @{locale particular_struct_sig} or
 in the @{locale ufo_particular_theory_sig} signatures,
 the corresponding symbols of the \<open>\<Gamma>\<^sub>1\<close> and \<open>\<Gamma>\<^sub>2\<close> structures can
 be referred to by prefixing with \<open>src.\<close> or \<open>tgt.\<close>. For example, 
 the set of possible worlds of \<open>\<Gamma>\<^sub>1\<close> and \<open>\<Gamma>\<^sub>2\<close> can be referred to,
 respectively, using the expressions \<open>src.\<W>\<close> and \<open>tgt.\<W>\<close>.
\<close>

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> particular_struct_morphism_sig =
  ufo_src_tgt_particular_models_sig 
  where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> 
    and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>   
  for 
    \<phi> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> and
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 

context \<^marker>\<open>tag aponly\<close> particular_struct_morphism_sig
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>In this context, let \<open>\<phi>\<close> denote a function from particulars of type
 @{typ \<open>'p\<^sub>1\<close>} to particulars of type @{typ \<open>'p\<^sub>2\<close>}. We call the signature
 composed of \<open>\<Gamma>\<^sub>1\<close>, \<open>\<Gamma>\<^sub>2\<close> and \<open>\<phi>\<close> a \emph{particular structure morphism}
 signature, referred to in the formal theory as 
 @{locale particular_struct_morphism_sig}. In the context of this signature we define the following symbols:
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The symbol \<open>\<P>\<^sub>i\<^sub>m\<^sub>g\<close> denotes the \emph{image} of the set of particulars
  of the source structure over the morphism function:\<close>
  
definition morph_image (\<open>\<P>\<^sub>i\<^sub>m\<^sub>g\<close>) where
  \<open>\<P>\<^sub>i\<^sub>m\<^sub>g \<equiv> \<phi> ` src.\<P>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The symbol \<open>\<phi>\<^sup>-\<^sup>1\<close> denotes a function from the type of particulars @{typ \<open>'p\<^sub>2\<close>}
  to the type of particulars @{typ \<open>'p\<^sub>1\<close>} such that it \emph{inverts} the morphism
  function \<open>\<phi>\<close> with regards to the set of particulars of the source structure:\<close>

abbreviation inv_morph (\<open>\<phi>\<inverse>\<close>) where
  \<open>\<phi>\<inverse> \<equiv> Inv src.\<P> \<phi>\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_I[intro]: 
  \<open>x \<in> src.\<P> \<Longrightarrow> \<phi> x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close>
  by (auto simp: morph_image_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_E[elim!]: 
  assumes \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close>
  obtains y where \<open>y \<in> src.\<P>\<close> \<open>x = \<phi> y\<close>
  using assms by (auto simp: morph_image_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_iff[simp]: 
  \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g \<longleftrightarrow> (\<exists>y \<in> src.\<P>. x = \<phi> y)\<close>
  by (auto simp: morph_image_def)

end \<^marker>\<open>tag aponly\<close>

subsection \<open>Axiomatization\<close>

locale \<^marker>\<open>tag aponly\<close> pre_particular_struct_morphism =
    particular_struct_morphism_sig 
    where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> 
      and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    src: particular_struct 
    where \<Gamma> = \<open>\<Gamma>\<^sub>1\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>1\<close> 
        and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  +
    tgt: particular_struct 
    where \<Gamma> = \<open>\<Gamma>\<^sub>2\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>2\<close> 
        and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>  +
  assumes 
    morphism_scope_substantials[intro!]: \<open>\<phi> \<in> src.\<S> \<rightarrow> tgt.\<S>\<close> and
    morphism_scope_moments[intro!]: \<open>\<phi> \<in> src.\<M> \<rightarrow> tgt.\<M>\<close> and
    morphism_extensional[intro!]: \<open>\<phi> \<in> extensional src.\<P>\<close> and
    quality_space_subset: 
      \<open>src.\<Q>\<S> \<subseteq> tgt.\<Q>\<S>\<close> and
(*    morph_preserves_particulars[intro]: 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> \<phi> x \<in> tgt.\<P>\<close> and    *)
    morph_reflects_inherence[simp]: 
      \<open>\<And>x y. \<lbrakk> x \<in> src.\<P> ; y \<in> src.\<P> \<rbrakk> \<Longrightarrow> 
              \<phi> x \<triangleleft>\<^sub>t \<phi> y \<longleftrightarrow> x \<triangleleft>\<^sub>s y\<close> and
(*    morph_does_not_add_bearers: 
      \<open>\<And>x z. \<lbrakk> x \<in> src.\<P> ; \<phi> x \<triangleleft>\<^sub>t z \<rbrakk> \<Longrightarrow> 
        \<exists>y \<in> src.\<P>.  z = \<phi> y\<close> and    *)
    morph_reflects_towardness[simp]: 
      \<open>\<And>x y. \<lbrakk> x \<in> src.\<P> ; y \<in> src.\<P> \<rbrakk> \<Longrightarrow>  
          \<phi> x \<longlongrightarrow>\<^sub>t \<phi> y \<longleftrightarrow> x \<longlongrightarrow>\<^sub>s y\<close> and
    morph_does_not_add_towards: 
      \<open>\<And>x z. \<lbrakk> x \<in> src.\<P> ;  \<phi> x \<longlongrightarrow>\<^sub>t z \<rbrakk> \<Longrightarrow> 
          \<exists>y \<in> src.\<P>. z = \<phi> y\<close> and
    morph_reflects_quale_assoc[simp]: 
      \<open>\<And>x q. x \<in> src.\<P> \<Longrightarrow> x \<leadsto>\<^sub>s q \<longleftrightarrow> \<phi> x \<leadsto>\<^sub>t q\<close> 
begin \<^marker>\<open>tag aponly\<close>

lemma morphism_scope_particulars[intro!]: \<open>\<phi> \<in> src.\<P> \<rightarrow> tgt.\<P>\<close>
  using morphism_scope_moments
        morphism_scope_substantials
        src.endurants_eq_un_moments_subst
  by auto

lemma  morph_preserves_particulars[intro]: 
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> \<phi> x \<in> tgt.\<P>\<close> 
  using morphism_scope_particulars by auto

lemma morph_does_not_add_bearers: 
  fixes x z
  assumes \<open>x \<in> src.\<P>\<close> \<open>\<phi> x \<triangleleft>\<^sub>t z\<close>
  shows \<open>\<exists>y \<in> src.\<P>.  z = \<phi> y\<close> 
proof -
  have A: \<open>\<phi> x \<in> tgt.\<M>\<close> using assms(2) by blast 
  have B: \<open>\<phi> x \<in> tgt.\<P>\<close> using assms(1) morphism_scope_particulars by auto
  have C: \<open>x \<in> src.\<M>\<close>
  proof (rule ccontr)
    assume \<open>x \<notin> src.\<M>\<close>
    then have \<open>x \<in> src.\<S>\<close> using assms(1) by blast
    then have \<open>\<phi> x \<in> tgt.\<S>\<close> using morphism_scope_substantials by blast
    then have \<open>\<phi> x \<notin> tgt.\<M>\<close> by blast
    then show False using A by blast
  qed
  then obtain y where \<open>x \<triangleleft>\<^sub>s y\<close> by blast
  then have \<open>\<phi> x \<triangleleft>\<^sub>t \<phi> y\<close> 
    by (meson src.inherence_scope morph_reflects_inherence
        src.inherence_axioms)
  then have \<open>z = \<phi> y\<close> using assms(2)
    by (metis tgt.\<M>_I tgt.bearer_ex1)
  then show ?thesis using assms(2) 
    by (metis \<open>x \<triangleleft>\<^sub>s y\<close> src.endurantI2)
qed

lemma pre_particular_struct_morphism_eqI:
  assumes 
    \<open>pre_particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<rho>\<close>
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> \<phi> x = \<rho> x\<close>
  shows \<open>\<phi> = \<rho>\<close>
proof
  fix x
  interpret \<rho>: pre_particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<rho> using assms by simp
  show \<open>\<phi> x = \<rho> x\<close>
  proof (cases \<open>x \<in> src.\<P>\<close>)
    assume \<open>x \<in> src.\<P>\<close>
    then show ?thesis using assms(2) by auto
  next
    assume \<open>x \<notin> src.\<P>\<close>
    then obtain \<open>\<phi> x = undefined\<close> \<open>\<rho> x = undefined\<close>
      using morphism_extensional \<rho>.morphism_extensional 
      by (meson extensional_arb)
    then show ?thesis by simp
  qed
qed

lemma pre_particular_struct_morphism_comp[intro!]:
  fixes \<Gamma>\<^sub>3 :: \<open>('p\<^sub>3,'q) particular_struct\<close>
  assumes \<open>pre_particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<rho>\<close>
  shows \<open>pre_particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 
          (\<rho> \<circ>\<^bsub>src.\<P>\<^esub>  \<phi>)\<close>
proof -
  let ?f = \<open>\<rho> \<circ>\<^bsub>src.\<P>\<^esub>  \<phi>\<close>
  interpret \<rho>: pre_particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<rho> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>3)\<close>
    using assms by simp
  show ?thesis
  proof (unfold_locales)
    show G1: \<open>?f \<in> src.\<S> \<rightarrow> \<rho>.tgt.\<S>\<close>
      using morphism_scope_substantials \<rho>.morphism_scope_substantials 
      by (smt (verit) PiE Pi_I compose_eq src.endurantI3)
    show G2: \<open>?f \<in> src.\<M> \<rightarrow> \<rho>.tgt.\<M>\<close>
      using morphism_scope_moments \<rho>.morphism_scope_moments
      by (smt (verit, ccfv_threshold) PiE Pi_I compose_eq src.endurantI1)
    show G3: \<open>?f \<in> extensional src.\<P>\<close>
      using morphism_extensional \<rho>.morphism_extensional by simp      
    show G4: \<open>src.\<Q>\<S> \<subseteq> \<rho>.tgt.\<Q>\<S>\<close>
      using quality_space_subset \<rho>.quality_space_subset by blast
    show G5: \<open>\<rho>.tgt_inheres_in (?f x) (?f y) \<longleftrightarrow> x \<triangleleft>\<^sub>s y\<close> 
      if as: \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> for x y
      using as morph_reflects_inherence \<rho>.morph_reflects_inherence      
      by (simp add: compose_eq morph_preserves_particulars)      
    show G6: \<open>\<rho>.tgt_towards (?f x) (?f y) \<longleftrightarrow> x \<longlongrightarrow>\<^sub>s y\<close>
      if as: \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> for x y
      using as morph_reflects_towardness \<rho>.morph_reflects_towardness
      by (simp add: compose_eq morph_preserves_particulars)      
    show G7: \<open>\<exists>y \<in> src.\<P>. z = ?f y\<close> 
      if as: \<open>x \<in> src.\<P>\<close> \<open>\<rho>.tgt_towards (?f x) z\<close> for x z
      using as morph_does_not_add_towards \<rho>.morph_does_not_add_towards
    proof -
      have A: \<open>?f x = \<rho> (\<phi> x)\<close> 
        using as(1) by (simp add: compose_eq)
      have B: \<open>?f x \<in> \<rho>.tgt.\<M>\<close> using as(2) by blast 
      then have C: \<open>x \<in> src.\<M>\<close> using G1 as(1) by blast
      then have D: \<open>x \<in> src.\<P>\<close> by blast
      then have E: \<open>\<phi> x \<in> tgt.\<P>\<close> by blast
      then obtain y\<^sub>1 where F: \<open>y\<^sub>1 \<in> tgt.\<P>\<close> \<open>z = \<rho> y\<^sub>1\<close> \<open>\<phi> x \<longlongrightarrow>\<^sub>t y\<^sub>1\<close>                 
        by (metis A \<rho>.morph_does_not_add_towards 
                    \<rho>.morph_reflects_towardness as(2))
      then obtain y\<^sub>2 where \<open>x \<in> src.\<P>\<close> \<open>y\<^sub>1 = \<phi> y\<^sub>2\<close> \<open>x \<longlongrightarrow>\<^sub>s y\<^sub>2\<close>        
        by (metis D morph_does_not_add_towards morph_reflects_towardness)
      then show ?thesis           
        by (metis F(2) compose_eq src.towardness_scopeD(3))
    qed
    show \<open>x \<leadsto>\<^sub>s q \<longleftrightarrow> \<rho>.tgt_assoc_quale (?f x) q\<close> 
      if as: \<open>x \<in> src.\<P>\<close> for x q
      using as morph_reflects_quale_assoc \<rho>.morph_reflects_quale_assoc
      by (simp add: compose_eq morph_preserves_particulars)      
  qed
qed

lemma undefined_not_in_img[simp]: \<open>undefined \<notin> \<phi> ` src.\<P>\<close>
proof (rule ccontr ; simp)
  assume \<open>undefined \<in> \<phi> ` src.\<P>\<close>
  then obtain x where A: \<open>x \<in> src.\<P>\<close> \<open>\<phi> x = undefined\<close>
    using imageE by metis
  have \<open>\<phi> x \<in> \<P>\<close> using A(1) 
    by (metis A(2) morph_preserves_particulars
        tgt.particulars_exist_in_some_world tgt.undefined_not_in_particulars)
  then have \<open>\<phi> x \<noteq> undefined\<close> 
    by (metis A(1) morph_preserves_particulars
        tgt.particulars_exist_in_some_world tgt.undefined_not_in_particulars)
  then show False using A(2) by simp
qed

end

lemma card_gt_1_ex:
  fixes x :: 'a
  assumes \<open>card (UNIV :: 'a set) \<noteq> 1\<close>
  shows \<open>\<exists>(y :: 'a). y \<noteq> x\<close>
proof -
  let ?U = \<open>UNIV :: 'a set\<close>
  show ?thesis
  proof (cases \<open>finite ?U\<close>)
    assume A: \<open>finite ?U\<close>    
    then have B: \<open>card ?U \<noteq> 0\<close> 
      by simp
    have C: \<open>1 < n\<close> if \<open>n \<noteq> 0\<close> \<open>n \<noteq> 1\<close> for n :: nat      
      using that by auto
    note [[show_types]]    
    have \<open>1 < card ?U\<close> using C B assms by metis
    then have \<open>0 < card (?U - {x})\<close> by (simp add: A)
    then obtain y where \<open>y \<in> ?U - {x}\<close> 
      by (metis all_not_in_conv card.empty less_nat_zero_code)
    then have \<open>y \<noteq> x\<close> by blast
    then show ?thesis by blast
  next
    assume A: \<open>\<not> finite ?U\<close>
    then have \<open>infinite ?U\<close> by blast
    then have \<open>infinite (?U - {x})\<close> by simp
    then have \<open>?U - {x} \<noteq> \<emptyset>\<close> by (metis finite.emptyI)
    then obtain y where \<open>y \<in> ?U - {x}\<close> by blast
    then have \<open>y \<noteq> x\<close> by blast
    then show ?thesis by blast
  qed
qed


context
  fixes \<Gamma> :: \<open>('p,'q) particular_struct\<close> and \<phi>
  assumes A: \<open>pre_particular_struct_morphism \<Gamma> \<Gamma> \<phi>\<close>
begin

interpretation pre_particular_struct_morphism \<Gamma> \<Gamma> \<phi> using A by simp
(*
lemma   
  assumes \<open>\<And>(\<rho> :: 'a \<Rightarrow> 'p). 
                pre_particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma> \<rho> \<Longrightarrow>
               compose (ParticularStructure.particulars \<Gamma>\<^sub>1) \<phi> \<rho> = \<rho>\<close>
          \<open>\<And>(\<rho> :: 'p \<Rightarrow> 'a). 
                pre_particular_struct_morphism \<Gamma> \<Gamma>\<^sub>1 \<rho> \<Longrightarrow>
                compose (ParticularStructure.particulars \<Gamma>) \<rho> \<phi> = \<rho>\<close>
          \<open>x \<in> src.\<P>\<close>
        shows \<open>\<phi> x = x\<close>
proof (rule ccontr)

  let ?U = \<open>UNIV :: 'p set\<close>
  show ?thesis

proof (cases \<open>card (UNIV :: 'p set) = 1\<close>)
  assume A: \<open>card (UNIV :: 'p set) = 1\<close>
  then have \<open>?U = {x}\<close> 
    by (metis (full_types) UNIV_I card_1_singletonE singletonD)
  then show ?thesis by blast
next
  assume A: \<open>card ?U \<noteq> 1\<close>     
  then obtain y where \<open>y \<noteq> x\<close>  
    using card_gt_1_ex[of x] by blast
  
  proof (cases \<open>finite ?U\<close>)
    assume \<open>finite ?U\<close>
    then have B: \<open>card ?U \<noteq> 0\<close> 
      by simp
    have C: \<open>1 < n\<close> if \<open>n \<noteq> 0\<close> \<open>n \<noteq> 1\<close> for n :: nat      
      using that by auto
    have \<open>1 < card (UNIV :: 'p set)\<close> using C[OF B A] 
    
  show ?thesis sorry
  
  oops
*)
text \<^marker>\<open>tag bodyonly\<close> \<open>
  Thus, to define a notion of morphism based on the function \<open>\<phi>\<close>, we need to define under
  what conditions can such a function be judged as a mapping that preserves the structure
  of the \<open>\<Gamma>\<^sub>1\<close> and \<open>\<Gamma>\<^sub>2\<close> structures. 
  As the choice of conditions is somewhat arbitrary, we need some guiding principles to  
  driver their specification. In this context, we call \<open>(\<phi>,\<Gamma>\<^sub>1 ,\<Gamma>\<^sub>2)\<close> a particular structure pre-morphism
  (formally a @{locale pre_particular_struct_morphism})  just in
  case the following conditions are met: 
 \<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{axiom}{$@{thm_name quality_space_subset}$}
Every quality space present in the source structure is also present in the target structure.
Formally: $@{thm quality_space_subset [no_vars]}$.
\end{axiom}  

\begin{axiom}{$@{thm_name morph_preserves_particulars}$}
The morphism \<open>\<phi>\<close> preserves \emph{particularity}, i.e. any particular of the source structure
is mapped to a particular in the target structure:
\[ @{thm morph_preserves_particulars [no_vars]} \]
\end{axiom}

\begin{axiom}{$@{thm_name morph_reflects_inherence}$}
The morphism \<open>\<phi>\<close> does not \emph{add} or \emph{change} inherence relations between
target particulars that are \<open>\<phi>\<close>-images of source particulars. In other words,
for any two particulars of the source structure, their corresponding image stand
in an \emph{inherence} relation if and only if they also stand in an inherence relation
in the source structure:
\[ @{thm morph_reflects_inherence [no_vars]} \]
\end{axiom}

\begin{axiom}{$@{thm_name morph_does_not_add_bearers}$}
The morphism \<open>\<phi>\<close> does not add bearers to substantials of the source structure. Equivalently,
 the image of a particular of the source structure has a bearer if and only if that bearer 
 is also the image of some source particular. This together with the 
 @{thm_name morph_reflects_inherence} axiom is equivalent to the first statement. Formally:
\[ @{thm morph_does_not_add_bearers [no_vars]} \]
\end{axiom}

\begin{axiom}{$@{thm_name morph_reflects_towardness}$}
The morphism \<open>\<phi>\<close> does not \emph{add} or \emph{change} ``towards'' relations between
target particulars that are \<open>\<phi>\<close>-images of source particulars. In other words,
for any two particulars of the source structure, their corresponding image stand
in a \emph{towards} relation if and only if they stand in a towards relation
in the source structure:
\[ @{thm morph_reflects_towardness [no_vars]} \]
\end{axiom}

\begin{axiom}{$@{thm_name morph_does_not_add_towards}$}
The morphism \<open>\<phi>\<close> does not add a \emph{towards} relation to images of source particulars. In other
words, a target moment that is the image of a source moment is directed ``towards'' another
target moment if and only if it is the image of some moment that was directed to some other
source moment:
\[ @{thm morph_does_not_add_towards [no_vars]} \]
\end{axiom}

\begin{axiom}{$@{thm_name morph_reflects_quale_assoc}$}
The morphism \<open>\<phi>\<close> preserves quale association of source particulars. If a source particular
is associated with some quale then its image is also associated with the same quale, and
vice-versa:
\[ @{thm morph_reflects_quale_assoc [no_vars]} \]
\end{axiom}

\<close>



end \<^marker>\<open>tag aponly\<close>


text \<^marker>\<open>tag bodyonly\<close> \<open>
  Besides the preservation conditions detailed in these axioms, the following preservation
lemmas are derivable from the same axioms:
 \<close>

context  \<^marker>\<open>tag aponly\<close> pre_particular_struct_morphism
begin \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_scope: \<open>\<P>\<^sub>i\<^sub>m\<^sub>g \<subseteq> tgt.\<P>\<close> 
  using morph_preserves_particulars by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_preserves_inherence_1[intro]: 
  assumes  \<open>x \<triangleleft>\<^sub>s y\<close>
  shows \<open>\<phi> x \<triangleleft>\<^sub>t \<phi> y\<close>
  using assms src.inherence_scope morph_reflects_inherence by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_preserves_substantials[simp]: 
  assumes \<open>x \<in> src.\<P>\<close>
  shows \<open>\<phi> x \<in> tgt.\<S> \<longleftrightarrow> x \<in> src.\<S>\<close>
proof -
  have \<open>(\<exists>y. \<phi> x \<triangleleft>\<^sub>t y) \<longleftrightarrow> (\<exists>y. x \<triangleleft>\<^sub>s y)\<close> 
    using assms morph_does_not_add_bearers morph_reflects_inherence by blast
  then show \<open>?thesis\<close>
    using assms by blast
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_preserves_substantials}$}
For any particular \<open>x\<close> of \<open>\<Gamma>\<^sub>1\<close> the following statements are logically equivalent:
\begin{itemize}
  \item{\<open>x\<close> is a substantial (in \<open>\<Gamma>\<^sub>1\<close>);}
  \item{\<open>\<phi> x\<close> is a substantial (in \<open>\<Gamma>\<^sub>2\<close>).}
\end{itemize}
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_preserves_moments[intro]: \<open>x \<in> src.\<M> \<Longrightarrow> \<phi> x \<in> tgt.\<M>\<close>  
  using morph_reflects_inherence by blast


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_preserves_moments_simp[simp]:
  assumes \<open>x \<in> src.\<P>\<close>
  shows \<open>\<phi> x \<in> tgt.\<M> \<longleftrightarrow> x \<in> src.\<M>\<close>  
  using morph_preserves_moments assms 
  using morph_preserves_substantials 
  by blast

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_preserves_moments_simp}$}
For any particular \<open>x\<close> of \<open>\<Gamma>\<^sub>1\<close> the following statements are logically equivalent:
\begin{itemize}
  \item{\<open>x\<close> is a moment (in \<open>\<Gamma>\<^sub>1\<close>);}
  \item{\<open>\<phi> x\<close> is a moment (in \<open>\<Gamma>\<^sub>2\<close>).}
\end{itemize}
\end{lemma}
\<close>


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_bearers[simp]: 
  assumes assms[simp,intro!]: \<open>x \<in> src.\<M>\<close>
  shows \<open>tgt.bearer (\<phi> x) = \<phi> (src.bearer x)\<close>
proof -
  have A[simp,intro!]: \<open>\<phi> x \<in> tgt.\<M>\<close> using assms by blast
  then obtain y where B: \<open>y \<in> src.\<P>\<close> \<open>\<phi> x \<triangleleft>\<^sub>t \<phi> y\<close> \<open>x \<triangleleft>\<^sub>s y\<close>    
    by (meson assms morph_preserves_inherence_1 src.bearer_ex1 src.endurantI1 src.endurantI2)
  then obtain \<open>tgt.bearer (\<phi> x)  = \<phi> y\<close> \<open>src.bearer x = y\<close>
    using tgt.bearer_eqI assms    
    by (simp add: src.bearer_eqI)
  then show \<open>?thesis\<close> using B by blast
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_reflects_bearers}$}
For any moment \<open>x\<close> of \<open>\<Gamma>\<^sub>1\<close>, the image of the bearer, in \<open>\<Gamma>\<^sub>1\<close>, of \<open>x\<close>  
is the bearer, in \<open>\<Gamma>\<^sub>2\<close>, of the image of \<open>x\<close>, i.e.
\[ @{thm morph_reflects_bearers} \]

\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_ultimate_bearers[simp]: 
  assumes \<open>x \<in> src.\<P>\<close>
  shows \<open>tgt.ultimateBearer (\<phi> x) = \<phi> (src.ultimateBearer x)\<close>
  using assms 
proof (induct \<open>x\<close> rule: wfP_induct[OF src.inherence_is_noetherian] ; simp)
  fix x
  assume as: \<open>\<forall>y. x \<triangleleft>\<^sub>s y \<longrightarrow> y \<in> src.\<P> \<longrightarrow> tgt.ultimateBearer (\<phi> y) = \<phi> (src.ultimateBearer y)\<close>
             \<open>x \<in> src.\<P>\<close>
  have A[simp]: \<open>tgt.ultimateBearer (\<phi> y) = \<phi> (src.ultimateBearer y)\<close> if \<open>x \<triangleleft>\<^sub>s y\<close> \<open>y \<in> src.\<P>\<close> for y
    using that as(1) by blast
  show \<open>tgt.ultimateBearer (\<phi> x) = \<phi> (src.ultimateBearer x)\<close>
  proof (cases \<open>x \<in> src.\<S>\<close>)
    assume \<open>x \<in> src.\<S>\<close>
    then have B: \<open>src.ultimateBearer x = x\<close> 
      using src.ultimate_bearer_eq_simp by auto
    have \<open>\<phi> x \<in> tgt.\<S>\<close> using \<open>x \<in> src.\<S>\<close> 
      by (simp add: as(2))
    then have \<open>tgt.ultimateBearer (\<phi> x) = \<phi> x\<close> 
      using tgt.ultimate_bearer_eq_simp by auto
    then show \<open>?thesis\<close> using B by simp
  next
    assume as1: \<open>x \<notin> src.\<S>\<close>
    then obtain B: \<open>x \<in> src.\<M>\<close> \<open>\<phi> x \<in> tgt.\<M>\<close> 
      using as(2) by blast
    then obtain y where C: \<open>y \<in> src.\<P>\<close> \<open>x \<triangleleft>\<^sub>s y\<close> \<open>\<phi> x \<triangleleft>\<^sub>t \<phi> y\<close>
      using morph_reflects_inherence morph_does_not_add_bearers src.inherence_scope by auto
    then have D[simp]: \<open>tgt.ultimateBearer (\<phi> y) = \<phi> (src.ultimateBearer y)\<close>
      using A by blast
    have Esrc[simp]: \<open>src.ultimateBearer x = src.ultimateBearer y\<close>
      apply (rule src.ultimate_bearer_eqI1)
      using C(2) by blast
    have Etgt[simp]: \<open>tgt.ultimateBearer (\<phi> x) = tgt.ultimateBearer (\<phi> y)\<close>
      apply (rule tgt.ultimate_bearer_eqI1)
      using C(3) by blast
    show \<open>?thesis\<close> by simp
  qed
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_reflects_ultimate_bearers}$}
For any particular \<open>x\<close> of \<open>\<Gamma>\<^sub>1\<close>, the image of the ultimate bearer, in \<open>\<Gamma>\<^sub>1\<close>, of \<open>x\<close>  
is the ultimate bearer, in \<open>\<Gamma>\<^sub>2\<close>, of the image of \<open>x\<close>, i.e.
\[ @{thm morph_reflects_ultimate_bearers} \]

\end{lemma}
\<close>

end \<^marker>\<open>tag (proof) aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  So far, the axioms presented in @{locale pre_particular_struct_morphism} 
  only describe restrictions on the elements of particular structures that
  characterize relationships of particular structure particulars. No 
  restrictions were imposed on the sets of possible world sets of 
  the source and target structure.

  Before we add such axioms, we need to determine what structural properties
  should be preserved by \<open>\<phi>\<close> when we say that ``\<open>\<phi>\<close> preserves 
  possible world structures''. Basically, we want to preserve the
  properties that are characterized by the set of possible worlds. Namely,
  we want to preserve the existential dependency and existential 
  independence of particulars. In other words, if a particular is 
  existentially dependent upon another in the source structure, than the image of
  the first should also be existentially dependent upon the image of the later. 
  Similarly, the image of particulars that are existentially independent
  in the source structure should also be independent in the target 
  structure.

  We frame this condition using the notion of correspondence between
  worlds. Given a world \<open>w\<^sub>s\<close> of the source structure and a world \<open>w\<^sub>t\<close> of the target
  structure, we say that \<open>w\<^sub>s\<close> and \<open>w\<^sub>t\<close> correspond, written as \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close>,
  if the image of \<open>w\<^sub>s\<close> under \<open>\<phi>\<close> corresponds to the largest subset of \<open>w\<^sub>t\<close> 
  that is the image of a subset of the set of particulars of the source
  structure. Phrased in another way, \<open>w\<^sub>s\<close> and \<open>w\<^sub>t\<close> correspond just in case,
  for every source particular \<open>x\<close>, \<open>x\<close> is in \<open>w\<^sub>s\<close> if and only if \<open>x\<close>'s image
  under \<open>\<phi>\<close> is in \<open>w\<^sub>t\<close>. Formally, we have:
\<close>

context \<^marker>\<open>tag aponly\<close> particular_struct_morphism_sig
begin \<^marker>\<open>tag aponly\<close>

definition world_corresp (infix \<open>\<Leftrightarrow>\<close> 75) where
  \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t \<equiv> w\<^sub>s \<in> src.\<W> \<and> w\<^sub>t \<in> tgt.\<W> \<and> 
             (\<forall>x \<in> src.\<P>. (x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t))\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> world_corresp_I[intro!]:
  assumes 
    \<open>w\<^sub>s \<in> src.\<W>\<close> \<open>w\<^sub>t \<in> tgt.\<W>\<close>
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
  shows \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close>
  using assms by (auto simp: world_corresp_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> world_corresp_E[elim!]:
  assumes \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close>
  obtains \<open>w\<^sub>s \<in> src.\<W>\<close> \<open>w\<^sub>t \<in> tgt.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
  using assms by (auto simp: world_corresp_def)

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> particular_struct_morphism =
    pre_particular_struct_morphism 
    where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> 
      and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close>  +
  assumes
    morph_worlds_correspond_src_tgt: 
      \<open>w\<^sub>s \<in> src.\<W> \<Longrightarrow> \<exists>w\<^sub>t. w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> and
    morph_worlds_correspond_tgt_src: 
      \<open>w\<^sub>t \<in> tgt.\<W> \<Longrightarrow> \<exists>w\<^sub>s. w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> 
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We can now complete the formal definition of a particular structure morphism
  by adding the following axioms to the previously introduced
  axioms, which state that every possible world in the source structure must have
  at least one corresponding possible world in the target structure, and
  vice-versa:
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{axiom}{$@{thm_name morph_worlds_correspond_src_tgt}$}
\[ @{thm morph_worlds_correspond_src_tgt [no_vars]} \]
\end{axiom}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  These axioms guarantee 
  that existential dependency and existential independence are preserved
  by \<open>\<phi>\<close>, as per the following lemmas:  
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_ed:
  \<open>src.ed x y \<longleftrightarrow> 
      x \<in> src.\<P> \<and> y \<in> src.\<P> 
      \<and> tgt.ed (\<phi> x) (\<phi> y)\<close>
proof (intro iffI conjI ; (elim conjE)?)
  assume \<open>src.ed x y\<close>
  then obtain A: \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> \<open>\<And>w. \<lbrakk> w \<in> src.\<W> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w\<close>
    by blast
  note A(1,2)[simp,intro!]
  show \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> by auto
  obtain B[simp,intro!]: \<open>\<phi> x \<in> tgt.\<P>\<close> \<open>\<phi> y \<in> tgt.\<P>\<close> by auto
  show \<open>tgt.ed (\<phi> x) (\<phi> y)\<close>
  proof (intro tgt.edI ; simp?)
    fix w\<^sub>t
    assume C[simp,intro!]: \<open>w\<^sub>t \<in> tgt.\<W>\<close> \<open>\<phi> x \<in> w\<^sub>t\<close>    
    obtain w\<^sub>s where D: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> using C morph_worlds_correspond_tgt_src by metis
    then obtain E[intro!,simp]: \<open>w\<^sub>s \<in> src.\<W>\<close> \<open>x \<in> w\<^sub>s\<close>
      using C(2) world_corresp_E by blast
    then have F[simp,intro!]: \<open>y \<in> w\<^sub>s\<close> using A(3) by blast
    then show \<open>\<phi> y \<in> w\<^sub>t\<close> using D world_corresp_E by blast
  qed
next
  assume A[simp,intro!]: \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> and B: \<open>tgt.ed (\<phi> x) (\<phi> y)\<close>
  then obtain A: \<open>\<And>w. \<lbrakk> w \<in> tgt.\<W> ; \<phi> x \<in> w \<rbrakk> \<Longrightarrow> \<phi> y \<in> w\<close>
    by blast  
  obtain B[simp,intro!]: \<open>\<phi> x \<in> tgt.\<P>\<close> \<open>\<phi> y \<in> tgt.\<P>\<close> by auto
  show \<open>src.ed x y\<close>
  proof (intro src.edI ; simp?)
    fix w\<^sub>s
    assume C[simp,intro!]: \<open>w\<^sub>s \<in> src.\<W>\<close> \<open>x \<in> w\<^sub>s\<close>    
    obtain w\<^sub>t where D: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> using C morph_worlds_correspond_src_tgt by metis
    then obtain E[intro!,simp]: \<open>w\<^sub>t \<in> tgt.\<W>\<close> \<open>\<phi> x \<in> w\<^sub>t\<close>
      using C(2) world_corresp_E by blast
    then have F[simp,intro!]: \<open>\<phi> y \<in> w\<^sub>t\<close> using A by blast
    then show \<open>y \<in> w\<^sub>s\<close> using D world_corresp_E by blast
  qed
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_ed_simp[simp]:
  assumes \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close>
  shows \<open>src.ed x y \<longleftrightarrow>  tgt.ed (\<phi> x) (\<phi> y)\<close>
  using assms morph_reflects_ed by blast
text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_reflects_ed_simp}$}
Given a particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close>, and
any \<open>\<Gamma>\<^sub>1\<close> particulars \<open>x\<close> and \<open>y\<close>, the following statements 
are logically equivalent:
\begin{itemize}
  \item{\<open>x\<close> and \<open>y\<close> are existentially dependent (in \<open>\<Gamma>\<^sub>1\<close>)}
  \item{\<open>\<phi> x\<close> and \<open>\<phi> y\<close> are existentially dependent (in \<open>\<Gamma>\<^sub>2\<close>)}
\end{itemize}
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_src_indep: \<open>src.indep x y \<longleftrightarrow> x \<in> src.\<P> \<and> y \<in> src.\<P> \<and> tgt.indep (\<phi> x) (\<phi> y)\<close>
  apply (auto simp add: src.indep_def tgt.indep_def)
  subgoal G1 for w\<^sub>1 w\<^sub>2
    by (meson morph_worlds_correspond_src_tgt world_corresp_def)
  subgoal G2 for w\<^sub>1 w\<^sub>2
    by (meson morph_worlds_correspond_src_tgt world_corresp_def)
  subgoal G3 for w\<^sub>1 w\<^sub>2    
    by (meson morph_worlds_correspond_tgt_src world_corresp_def)
  subgoal G4 for w\<^sub>1 w\<^sub>2    
    by (meson morph_worlds_correspond_tgt_src world_corresp_def)
  done


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_reflects_src_indep_simp[simp]:
  assumes \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> 
  shows \<open>tgt.indep (\<phi> x) (\<phi> y) \<longleftrightarrow> src.indep x y\<close>
  using assms morph_reflects_src_indep by auto

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_reflects_src_indep_simp}$}
Given a particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close>, and
any \<open>\<Gamma>\<^sub>1\<close> particulars \<open>x\<close> and \<open>y\<close>, the following statements 
are logically equivalent:
\begin{itemize}
  \item{\<open>x\<close> and \<open>y\<close> are existentially independent (in \<open>\<Gamma>\<^sub>1\<close>)}
  \item{\<open>\<phi> x\<close> and \<open>\<phi> y\<close> are existentially independent (in \<open>\<Gamma>\<^sub>2\<close>)}
\end{itemize}
\end{lemma}
\<close>

end \<^marker>\<open>tag aponly\<close>

subsection \<open>The Category of Particular Structures\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  One of the properties of particular struct morphisms is that they are 
  closed under composition:
\<close>

context
  fixes
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
    \<Gamma>\<^sub>3 :: \<open>('p\<^sub>3,'q) particular_struct\<close> and
    \<phi>\<^sub>1\<^sub>2 :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> and
    \<phi>\<^sub>2\<^sub>3 :: \<open>'p\<^sub>2 \<Rightarrow> 'p\<^sub>3\<close> 
  assumes bassms:
    \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2\<close>
    \<open>particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3\<close>
begin

interpretation M2: particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3
  using \<open>particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3\<close> .

interpretation M1: particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2
  using \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2\<close> .

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_morphism_comp:
    \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2)\<close>
proof \<^marker>\<open>tag (proof) aponly\<close> -
  
  interpret M12: pre_particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 \<open>\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2\<close>
    using M1.pre_particular_struct_morphism_comp
          M2.pre_particular_struct_morphism_axioms
    by metis
  
  have m12_morph_worlds_correspond_src_tgt:
     \<open>\<exists>w\<^sub>t. M12.world_corresp w\<^sub>s w\<^sub>t\<close> if A[simp]: \<open>w\<^sub>s \<in> M1.src.\<W>\<close> for w\<^sub>s
  proof -
    obtain w\<^sub>2 where \<open>M1.world_corresp w\<^sub>s w\<^sub>2\<close> 
      using A M1.morph_worlds_correspond_src_tgt by fastforce
    then obtain 
        B[simp]: \<open>w\<^sub>2 \<in> M2.src.\<W>\<close> 
          \<open>\<And>x. x \<in> M1.src.\<P> \<Longrightarrow> \<phi>\<^sub>1\<^sub>2 x \<in> w\<^sub>2 \<longleftrightarrow> x \<in> w\<^sub>s\<close>
      using M1.world_corresp_E by metis
    obtain w\<^sub>t where \<open>M2.world_corresp w\<^sub>2 w\<^sub>t\<close> 
      using M2.morph_worlds_correspond_src_tgt[OF B(1)] by metis
    then  obtain C[simp]: \<open>w\<^sub>t \<in> M2.tgt.\<W>\<close> 
        \<open>\<And>x. x \<in> M2.src.\<P> \<Longrightarrow> \<phi>\<^sub>2\<^sub>3 x \<in> w\<^sub>t \<longleftrightarrow> x \<in> w\<^sub>2\<close>
      using M2.world_corresp_E by blast
    show ?thesis
      apply (intro exI[of _ w\<^sub>t] M12.world_corresp_I ; simp?)            
      by (simp add: M1.morph_preserves_particulars compose_eq)
  qed
    
  have m12_morph_worlds_correspond_tgt_src:
      \<open>\<exists>w\<^sub>s. M12.world_corresp w\<^sub>s w\<^sub>t\<close> if A[simp]: \<open>w\<^sub>t \<in> M2.tgt.\<W>\<close> for w\<^sub>t 
  proof -
    obtain w\<^sub>2 where \<open>M2.world_corresp w\<^sub>2 w\<^sub>t\<close> 
      using A M2.morph_worlds_correspond_tgt_src by fastforce
    then obtain 
        B[simp]: \<open>w\<^sub>2 \<in> M2.src.\<W>\<close> 
          \<open>\<And>x. x \<in> M2.src.\<P> \<Longrightarrow> \<phi>\<^sub>2\<^sub>3 x \<in> w\<^sub>t \<longleftrightarrow> x \<in> w\<^sub>2\<close>
      using M2.world_corresp_E by metis
    obtain w\<^sub>s where \<open>M1.world_corresp w\<^sub>s w\<^sub>2\<close> 
      using M1.morph_worlds_correspond_tgt_src[OF B(1)] by metis
    then obtain C[simp]: \<open>w\<^sub>s \<in> M1.src.\<W>\<close> 
        \<open>\<And>x. x \<in> M1.src.\<P> \<Longrightarrow> \<phi>\<^sub>1\<^sub>2 x \<in> w\<^sub>2 \<longleftrightarrow> x \<in> w\<^sub>s\<close>
      using M1.world_corresp_E by blast
    show ?thesis
      apply (intro exI[of _ w\<^sub>s] M12.world_corresp_I ; simp?)            
      by (simp add: M1.morph_preserves_particulars compose_eq)
  qed

  show ?thesis
    apply (unfold_locales)
    subgoal using m12_morph_worlds_correspond_src_tgt .
    subgoal using m12_morph_worlds_correspond_tgt_src .
    done
qed

context
fixes
    \<Gamma>\<^sub>4 :: \<open>('p\<^sub>4,'q) particular_struct\<close> and
    \<phi>\<^sub>3\<^sub>4 :: \<open>'p\<^sub>3 \<Rightarrow> 'p\<^sub>4\<close> 
  assumes m34:
    \<open>particular_struct_morphism \<Gamma>\<^sub>3 \<Gamma>\<^sub>4 \<phi>\<^sub>3\<^sub>4\<close>
begin

interpretation M3: particular_struct_morphism \<Gamma>\<^sub>3 \<Gamma>\<^sub>4 \<phi>\<^sub>3\<^sub>4 using m34 .

lemma morph_associative: 
      \<open>\<phi>\<^sub>3\<^sub>4 \<circ>\<^bsub>M1.src.\<P>\<^esub> (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2) = 
       (\<phi>\<^sub>3\<^sub>4 \<circ>\<^bsub>M2.src.\<P>\<^esub> \<phi>\<^sub>2\<^sub>3) \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2\<close>
  apply (intro comp_map_associative)  
  using M1.morph_image_def M1.morph_scope by presburger

end

end

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name particular_struct_morphism_comp}$}
For any morphisms @{term[show_types] \<open>\<phi>\<^sub>1\<^sub>2 :: 'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>}, 
from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close>, and
@{term[show_types] \<open>\<phi>\<^sub>2\<^sub>3 :: 'p\<^sub>2 \<Rightarrow> 'p\<^sub>3\<close>}, from \<open>\<Gamma>\<^sub>2\<close> to \<open>\<Gamma>\<^sub>3\<close>,
 the functional composition of \<open>\<phi>\<^sub>1\<^sub>2\<close> and \<open>\<phi>\<^sub>2\<^sub>3\<close> is a morphism from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>3\<close>.
\end{lemma}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Furthermore, the identity function serves as an identity morphism for
  every particular structure:
\<close>



context \<^marker>\<open>tag aponly\<close> particular_struct
begin \<^marker>\<open>tag aponly\<close>


lemma \<^marker>\<open>tag (proof) aponly\<close> (in particular_struct) id_is_a_morphism[intro!]:  
  \<open>particular_struct_morphism \<Gamma> \<Gamma> (id_on \<P>)\<close>
proof \<^marker>\<open>tag (proof) aponly\<close> -
  show ?thesis
    apply (unfold_locales ; auto?)
    subgoal for x
      by (subst id_on_eq(1)[of x endurants] ; blast)    
    subgoal for w
      by (intro exI[of _ w] ; auto simp: id_on_def particular_struct_morphism_sig.world_corresp_def)
    subgoal for w
      by (intro exI[of _ w] ; auto simp: particular_struct_morphism_sig.world_corresp_def)
    done
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name id_is_a_morphism}$}
For any @{term[show_types] \<open>\<Gamma> :: ('p,'q) particular_struct\<close>}, the identity function
on the set of particulars of \<open>\<Gamma>\<close> is a morphism of \<open>\<Gamma>\<close>:
\[ @{thm id_is_a_morphism [no_vars]} \]
\end{lemma}
\<close>



text \<^marker>\<open>tag bodyonly\<close> \<open>
   Since the class of particular structure morphisms is a subclass of the class functions
   that is closed under composition, they are also associative, i.e.    
      \[ \<open>(\<phi>\<^sub>3\<^sub>4 \<circ> \<phi>\<^sub>2\<^sub>3) \<circ> \<phi>\<^sub>1\<^sub>2 = \<phi>\<^sub>3\<^sub>4 \<circ> (\<phi>\<^sub>2\<^sub>3 \<circ> \<phi>\<^sub>1\<^sub>2)\<close> \]
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
   By the same token, identity functions (@{term[show_types] \<open>\<lambda>(x :: 't). x\<close>})), being
   particular structure morphisms for any particular structure whose particular type is
   @{typ \<open>'t\<close>}, are left and right identities for the composition of morphisms:
     \begin{align*}
     @{thm id_o[of \<phi>]} \\
     @{thm o_id[of \<phi>]}
    \end{align*}
\<close>
end  \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
   Thus, the class of particular structures and particular structure morphisms  
   can be considered a \emph{category}, i.e. for any type @{typ \<open>'q\<close>} of qualia 
   we have a category that:
   \begin{itemize}
     \item{
        the objects are the particular structures whose particular type is @{typ \<open>'p\<close>}
        for any @{typ \<open>'p\<close>};
     }
     \item {
        the set of morphisms between  
        @{term[show_types] \<open>\<Gamma>\<^sub>1 :: ('p\<^sub>1,'q) particular_struct\<close>} and
        @{term[show_types] \<open>\<Gamma>\<^sub>2 :: ('p\<^sub>2,'q) particular_struct\<close>} is
        the set of functions of the form @{term[show_types] \<open>\<phi> :: 'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>} that
        satisfy the conditions for a particular structure morphism, i.e. 
        that satisfy @{prop \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<close>};
     }
     \item {
        for any pair @{term[show_types] \<open>\<phi>\<^sub>1 :: 'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>} and 
          @{term[show_types] \<open>\<phi>\<^sub>2 :: 'p\<^sub>2 \<Rightarrow> 'p\<^sub>3\<close>} of morphisms
          between particular structures \<open>\<Gamma>\<^sub>1\<close>, \<open>\<Gamma>\<^sub>2\<close> and \<open>\<Gamma>\<^sub>3\<close>, their
          composition is given by function composition;
     }
     \item {
        for any @{term[show_types] \<open>\<Gamma> :: ('p,'q) particular_struct\<close>}, the
        identity function @{term[show_types] \<open>\<lambda>x :: 'p. x\<close>} is the identity
        for \<open>\<Gamma>\<close>;
      }
     \item {
        composition of particular structure morphisms is associative;
     }
     \item {
        composition of particular structure morphisms satisfy left and right 
        unit laws, i.e. @{prop \<open>id \<circ> \<phi> = \<phi>\<close>} and @{prop \<open>\<phi> \<circ> id = \<phi>\<close>}.
     }      
   \end{itemize}
\<close>
  
  
subsection \<open>Classes of Particular Structure Morphisms\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  By using the concepts of injective, surjective and bijective functions, and by borrowing
  the notions of \emph{endomorphism} and of \emph{permutations}, we can classify the class
  of particular structure morphisms into corresponding subclasses that are relevant for 
  the theories developed later in this thesis.

  These classes are characterized by the following axioms:
\<close>

locale \<^marker>\<open>tag aponly\<close> particular_struct_injection =
    particular_struct_morphism where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close>  +
  assumes 
    morph_is_injective[intro!,simp]: \<open>inj_on \<phi> src.\<P>\<close>

begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
A particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close> is an injective  
morphism if and only if it satisfies the following axiom:

\begin{axiom}{$@{thm_name morph_is_injective}$}
  the morphism is injective on the set of particulars of \<open>\<Gamma>\<^sub>1\<close>, i.e.
  \[ @{thm morph_is_injective [THEN inj_onD, no_vars] } \]
\end{axiom}
\<close>
end \<^marker>\<open>tag aponly\<close>


locale \<^marker>\<open>tag aponly\<close> particular_struct_surjection =
    particular_struct_morphism where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close>  +
  assumes 
    morph_is_surjective[simp]: \<open>\<phi> ` src.\<P> = tgt.\<P>\<close> 

begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open> 
A particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close> is an surjective  
morphism if and only if it satisfies the following axiom:

\begin{axiom}{$@{thm_name morph_is_surjective}$}
  the morphism is surjective from the set of particulars of \<open>\<Gamma>\<^sub>1\<close>, to
  the set of particulars of \<open>\<Gamma>\<^sub>2\<close>, i.e.
  \[ @{thm morph_is_surjective } \]
\end{axiom}
\<close>

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close>  particular_struct_bijection =
    particular_struct_injection where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> + 
    particular_struct_surjection where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
      Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
      Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close>  
begin

text \<^marker>\<open>tag bodyonly\<close> \<open> 
A particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close> is an 
called an isomorphism (@{locale particular_struct_bijection}) just in 
case it is both an injective morphism and a surjective morphism.
\<close>

end


locale \<^marker>\<open>tag aponly\<close> particular_struct_endomorphism_sig =
    particular_struct_morphism_sig where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<close> and \<Gamma>\<^sub>2 = \<open>\<Gamma>\<close> and \<phi> = \<open>\<phi>\<close>
        and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    particular_struct_defs where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>    
  for
    \<phi> :: \<open>'p \<Rightarrow> 'p\<close> and
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 
  

text \<^marker>\<open>tag bodyonly\<close> \<open>
  A particular structure morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>1\<close> to \<open>\<Gamma>\<^sub>2\<close> is
  called an endomorphism (@{locale particular_struct_endomorphism_sig})
  if and only if \<open>\<Gamma>\<^sub>1 = \<Gamma>\<^sub>2\<close>.
\<close>

context \<^marker>\<open>tag aponly\<close> particular_struct_endomorphism_sig
begin \<^marker>\<open>tag aponly\<close>

notation \<^marker>\<open>tag aponly\<close> inv_morph (\<open>\<phi>\<inverse>\<close>)

abbreviation endurants (\<open>\<P>\<close>) 
  where \<open>\<P> \<equiv> src.endurants\<close>

notation \<^marker>\<open>tag aponly\<close> world_corresp (infix \<open>\<Leftrightarrow>\<close> 75)
notation \<^marker>\<open>tag aponly\<close> tgt_inheres_in (infix \<open>\<triangleleft>\<close> 75)
notation \<^marker>\<open>tag aponly\<close> tgt_towards (infix \<open>\<longlongrightarrow>\<close> 75)
notation \<^marker>\<open>tag aponly\<close> tgt_assoc_quale (infix \<open>\<leadsto>\<close> 75)

abbreviation \<^marker>\<open>tag aponly\<close> qualifiedParticulars (\<open>\<P>\<^sub>q\<close>)
  where \<open>\<P>\<^sub>q \<equiv> src.qualifiedParticulars\<close>

abbreviation \<^marker>\<open>tag aponly\<close> \<open>\<P>\<^sub>i\<^sub>m\<^sub>g \<equiv> \<phi> ` \<P>\<close>

notation \<^marker>\<open>tag aponly\<close> src.\<S> (\<open>\<S>\<close>)
notation \<^marker>\<open>tag aponly\<close> src.\<M> (\<open>\<M>\<close>)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Since, in the context of an endomorphism, the source structure 
  is equal to the target structure, we can used the symbols that
  are using in the context of a particular structure without 
  ambiguity, e.g. \<open>\<P>\<close>, \<open>(\<Leftrightarrow>)\<close>, \<open>(\<triangleleft>)\<close>, \<open>(\<longlongrightarrow>)\<close>, \<open>(\<leadsto>)\<close>, \<open>\<S>\<close> and \<open>\<M>\<close>.
\<close>
  
end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> particular_struct_endomorphism =
    particular_struct_endomorphism_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  +
    particular_struct where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  +
    particular_struct_morphism where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<close> and \<Gamma>\<^sub>2 = \<open>\<Gamma>\<close> and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>  
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 


text \<^marker>\<open>tag bodyonly\<close> \<open>
  A morphism \<open>\<phi>\<close> is called a \emph{permutation morphism} just in case
  it is both an endomorphism and also a bijective morphism.
\<close>

locale \<^marker>\<open>tag aponly\<close> particular_struct_permutation =
    particular_struct_endomorphism where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    particular_struct_bijection where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<close> and \<Gamma>\<^sub>2 = \<open>\<Gamma>\<close> and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>


context
  fixes
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
    \<Gamma>\<^sub>3 :: \<open>('p\<^sub>3,'q) particular_struct\<close> and
    \<phi>\<^sub>1\<^sub>2 :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> and
    \<phi>\<^sub>2\<^sub>3 :: \<open>'p\<^sub>2 \<Rightarrow> 'p\<^sub>3\<close>

begin

interpretation M1: particular_struct_morphism_sig \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close> \<open>\<phi>\<^sub>1\<^sub>2\<close> .
interpretation M2: particular_struct_morphism_sig \<open>\<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>3\<close> \<open>\<phi>\<^sub>2\<^sub>3\<close> .

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_injection_comp:
  assumes 
    \<open>particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2\<close> 
    \<open>particular_struct_injection \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3\<close>
  shows \<open>particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2)\<close>
proof -
  interpret M1: particular_struct_injection \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close> \<open>\<phi>\<^sub>1\<^sub>2\<close> using assms(1) .
  interpret M2: particular_struct_injection \<open>\<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>3\<close> \<open>\<phi>\<^sub>2\<^sub>3\<close> using assms(2) .

  interpret particular_struct_morphism \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>3\<close> \<open>\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2\<close> 
    using particular_struct_morphism_comp
      M1.particular_struct_morphism_axioms 
      M2.particular_struct_morphism_axioms
    by metis

  show \<open>?thesis\<close>
    apply (unfold_locales)
    using M1.morph_is_injective M2.morph_is_injective 
    apply (intro inj_comp_map ; simp?)
    apply (rule inj_on_subset[of \<phi>\<^sub>2\<^sub>3 M1.tgt.endurants] ; simp?)
    by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_surjection_comp:
  assumes
    \<open>particular_struct_surjection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2\<close>
    \<open>particular_struct_surjection \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3\<close>
  shows
    \<open>particular_struct_surjection \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2)\<close>
proof -
  interpret M1: particular_struct_surjection \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close> \<open>\<phi>\<^sub>1\<^sub>2\<close> using assms by simp
  interpret M2: particular_struct_surjection \<open>\<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>3\<close> \<open>\<phi>\<^sub>2\<^sub>3\<close> using assms by simp

  interpret particular_struct_morphism \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>3\<close> \<open>\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2\<close>
    using particular_struct_morphism_comp 
      M1.particular_struct_morphism_axioms M2.particular_struct_morphism_axioms 
    by metis
  show \<open>?thesis\<close>
    apply (unfold_locales)    
    apply (simp only: map_comp_img_eq_comp_imp[of \<open>M1.src.\<P>\<close> \<open>M1.src.\<P>\<close> \<phi>\<^sub>2\<^sub>3])
    using M2.morph_is_surjective[simplified M1.morph_is_surjective[symmetric]]    
    by (metis image_comp)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_bijection_comp:
  assumes
    \<open>particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1\<^sub>2\<close>
    \<open>particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2\<^sub>3\<close>
  shows
    \<open>particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>M1.src.\<P>\<^esub> \<phi>\<^sub>1\<^sub>2)\<close>
  using assms particular_struct_bijection_def
    particular_struct_injection_comp
    particular_struct_surjection_comp
  by smt

end

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_endomorphism_comp:
  fixes \<Gamma> and \<phi>\<^sub>1 \<phi>\<^sub>2
  assumes
    \<open>particular_struct_endomorphism \<Gamma> \<phi>\<^sub>1\<close>
    \<open>particular_struct_endomorphism \<Gamma> \<phi>\<^sub>2\<close>
  shows
    \<open>particular_struct_endomorphism \<Gamma> (\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1)\<close>  
  using assms particular_struct_endomorphism_def
        particular_struct_morphism_comp
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_permutation_comp:
  fixes  \<Gamma> and  \<phi>\<^sub>1 \<phi>\<^sub>2
  assumes
    \<open>particular_struct_permutation \<Gamma> \<phi>\<^sub>1\<close>
    \<open>particular_struct_permutation \<Gamma> \<phi>\<^sub>2\<close>
  shows
    \<open>particular_struct_permutation \<Gamma> (\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1)\<close>  
  by (meson assms particular_struct_permutation_def 
            particular_struct_bijection_comp
            particular_struct_endomorphism_comp)
  

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The following sets represent the collections of
  morphisms that fall into each morphism class:
 \<close>


definition morphs (\<open>Morphs\<^bsub>_,_\<^esub>\<close> [999,999] 1000) where 
 \<open>Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<equiv> {\<phi> . particular_struct_morphism \<Gamma> \<Gamma>' \<phi> }\<close>

definition injectives (\<open>InjMorphs\<^bsub>_,_\<^esub>\<close> [999,999] 1000) where 
 \<open>InjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<equiv> {\<phi> . particular_struct_injection \<Gamma> \<Gamma>' \<phi> }\<close>

definition surjectives (\<open>SurjMorphs\<^bsub>_,_\<^esub>\<close> [999,999] 1000) where 
 \<open>SurjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<equiv> {\<phi> . particular_struct_surjection \<Gamma> \<Gamma>' \<phi> }\<close>

definition bijectives (\<open>BijMorphs\<^bsub>_,_\<^esub>\<close> [999,999] 1000) where 
 \<open>BijMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<equiv> {\<phi> . particular_struct_bijection \<Gamma> \<Gamma>' \<phi> }\<close>

definition endomorphisms (\<open>EndoMorphs\<^bsub>_\<^esub>\<close> [999] 1000) where
 \<open>EndoMorphs\<^bsub>\<Gamma>\<^esub> \<equiv> {\<phi> . particular_struct_endomorphism \<Gamma> \<phi> }\<close>

definition permutations (\<open>Perms\<^bsub>_\<^esub>\<close> [999] 1000) where
 \<open>Perms\<^bsub>\<Gamma>\<^esub> \<equiv> {\<phi> . particular_struct_permutation \<Gamma> \<phi> }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morphs_I[intro!]: 
  \<open>particular_struct_morphism \<Gamma> \<Gamma>' \<phi> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>
  by (auto simp: morphs_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> morphs_D[dest!]: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> particular_struct_morphism \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: morphs_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> morphs_iff[simp]: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<longleftrightarrow> particular_struct_morphism \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: morphs_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> injectives_I[intro!]: 
  \<open>particular_struct_injection \<Gamma> \<Gamma>' \<phi> \<Longrightarrow> \<phi> \<in> InjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>
  by (auto simp: injectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> injectives_D[dest!]: 
  \<open>\<phi> \<in> InjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> particular_struct_injection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: injectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> injectives_iff[simp]: \<open>\<phi> \<in> InjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<longleftrightarrow> particular_struct_injection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: injectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> surjectives_I[intro!]:
  \<open>particular_struct_surjection \<Gamma> \<Gamma>' \<phi> \<Longrightarrow> \<phi> \<in> SurjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>
  by (auto simp: surjectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> surjectives_D[dest!]: 
  \<open>\<phi> \<in> SurjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> particular_struct_surjection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: surjectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> surjectives_iff[simp]: 
  \<open>\<phi> \<in> SurjMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<longleftrightarrow> particular_struct_surjection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: surjectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijectives_I[intro!]:
  \<open>particular_struct_bijection \<Gamma> \<Gamma>' \<phi> \<Longrightarrow> \<phi> \<in> BijMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub>\<close>
  by (auto simp: bijectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijectives_D[dest!]: 
  \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<Longrightarrow> particular_struct_bijection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: bijectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijectives_iff[simp]: 
  \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>,\<Gamma>'\<^esub> \<longleftrightarrow> particular_struct_bijection \<Gamma> \<Gamma>' \<phi>\<close>
  by (auto simp: bijectives_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> endomorphisms_I[intro!]: \<open>particular_struct_endomorphism \<Gamma> \<phi> \<Longrightarrow> \<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
  by (auto simp: endomorphisms_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> endomorphisms_D[dest!]: \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> particular_struct_endomorphism \<Gamma> \<phi>\<close>
  by (auto simp: endomorphisms_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> endomorphisms_iff[simp]: \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub> \<longleftrightarrow> particular_struct_endomorphism \<Gamma> \<phi>\<close>
  by (auto simp: endomorphisms_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_I[intro!]: \<open>particular_struct_permutation \<Gamma> \<phi> \<Longrightarrow> \<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close> 
  by (auto simp: permutations_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_D[dest!]: \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> particular_struct_permutation \<Gamma> \<phi>\<close> 
  by (auto simp: permutations_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_iff[simp]: \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<longleftrightarrow> particular_struct_permutation \<Gamma> \<phi>\<close> 
  by (auto simp: permutations_def)


abbreviation \<^marker>\<open>tag aponly\<close> \<open>invMorph \<equiv> particular_struct_morphism_sig.inv_morph\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morphisms_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> ; \<phi>\<^sub>b \<in> Morphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub> \<rbrakk> \<Longrightarrow> 
    \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>a \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>  
  by (simp add: particular_struct_morphism_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> injective_morphisms_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> ; \<phi>\<^sub>b \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub> \<rbrakk> \<Longrightarrow> 
    \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>a \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>  
  by (simp add: particular_struct_injection_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> surjective_morphisms_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> ; \<phi>\<^sub>b \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub> \<rbrakk> \<Longrightarrow> 
    \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>a \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>  
  by (simp add: particular_struct_surjection_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijective_morphisms_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> ; \<phi>\<^sub>b \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub> \<rbrakk> \<Longrightarrow> 
    \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>a \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>  
  by (simp add: particular_struct_bijection_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> endomorphisms_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub> ; \<phi>\<^sub>b \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> 
  \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>a \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>  
  by (simp add: particular_struct_endomorphism_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_closed_under_comp[intro]:
  \<open>\<lbrakk> \<phi>\<^sub>a \<in> Perms\<^bsub>\<Gamma>\<^esub> ; \<phi>\<^sub>b \<in> Perms\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> 
    \<phi>\<^sub>b \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>a \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close>  
  by (simp add: particular_struct_permutation_comp)

lemma \<^marker>\<open>tag (proof) aponly\<close> injections_are_morphisms: 
  \<open>\<phi> \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
  by (simp add: particular_struct_injection_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> surjections_are_morphisms: 
  \<open>\<phi> \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
  by (simp add: particular_struct_surjection_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_are_injections_and_surjections:   
    \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<longleftrightarrow> \<phi> \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<and> \<phi> \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>  
  by (simp add: particular_struct_bijection_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_eq_injections_int_surjections:   
    \<open>BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> = InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<inter> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>  
  by (intro set_eqI ; simp only: Int_iff bijections_are_injections_and_surjections )

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_are_injections: 
  \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<Longrightarrow> \<phi> \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
  by (simp add: bijections_are_injections_and_surjections particular_struct_bijection_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_are_surjections: 
  \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<Longrightarrow> \<phi> \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
  by (simp add: bijections_are_injections_and_surjections particular_struct_bijection_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_are_morphisms: 
  \<open>\<phi> \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
  using bijections_are_injections
        injections_are_morphisms 
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> endormorphisms_are_morphisms: 
  \<open>Morphs\<^bsub>\<Gamma>,\<Gamma>\<^esub> = EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
  apply (intro set_eqI)
  by (simp add: endomorphisms_def particular_struct_endomorphism_def 
          particular_struct_morphism_def
          pre_particular_struct_morphism_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_endomorphisms: 
  \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> \<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
  by (simp add: particular_struct_permutation_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_bijections: 
  \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> \<phi> \<in> BijMorphs\<^bsub>\<Gamma>,\<Gamma>\<^esub>\<close>
  by (simp add: particular_struct_permutation_def)
     

text \<^marker>\<open>tag bodyonly\<close> \<open>
 For each morphism class, we can derive a useful set of lemmas. We highlight some
 of those here, but the reader is referred to the full Isabelle/HOL code for
 the complete collection:\<close>

context \<^marker>\<open>tag aponly\<close> particular_struct_injection
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 The main feature of the class of injective morphisms is the existence of an inverse
 for the morphism function. The morphism and its inverse determine a bijection 
 between the set of particulars of the source structure and its image on the set of
 particulars of the target structure. The properties regarding the injective morphism
 and its inverse are shown in the following lemmas.
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_morph[simp]:
  assumes \<open>x \<in> src.\<P>\<close>
  shows \<open>\<phi>\<inverse> (\<phi> x) = x\<close>
  using Inv_eq[OF morph_is_injective,OF assms] by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name inv_morph_morph}$}
    For any injective morphism function, its inverse into the set of particulars of the
    source structure is well defined and works as a left-inverse (or a retraction):

    \[ @{thm inv_morph_morph} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_bij_on_img[intro!,simp]: 
  \<open>bij_betw \<phi> src.\<P> \<P>\<^sub>i\<^sub>m\<^sub>g\<close>
  apply (simp only: morph_image_def)
  by (intro inj_on_imp_bij_betw ; simp)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name morph_bij_on_img}$}
  As an injective function, the morphism is a bijection to its image:
  \[ @{thm morph_bij_on_img } \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_inv_img[simp]: 
  \<open>\<phi>\<inverse> ` \<P>\<^sub>i\<^sub>m\<^sub>g = src.\<P>\<close>  
  using Inv_inj_surj[OF morph_is_injective] morph_image_def 
  by simp
  

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name phi_inv_img}$}
  Since \<open>\<phi>\<close> is injective, its inverse is a surjection from \<open>\<phi>\<close>'s image
  to the source set of particulars:
  \[ @{thm phi_inv_img } \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_inv_scope[intro]: \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g \<Longrightarrow> \<phi>\<inverse> x \<in> src.\<P>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_inv_inj_on_I_img[intro!,simp]: \<open>inj_on \<phi>\<inverse> \<P>\<^sub>i\<^sub>m\<^sub>g\<close>  
  by (simp add: inj_on_def morph_image_def)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name phi_inv_inj_on_I_img}$}
  The inverse is injective on the image of the morphism \<open>\<phi>\<close>:

  \[ @{thm phi_inv_inj_on_I_img} \]

  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_inv_bij_on_src_I[intro!,simp]: 
  \<open>bij_betw \<phi>\<inverse> \<P>\<^sub>i\<^sub>m\<^sub>g src.\<P> \<close>
  by (simp add: morph_image_def)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name phi_inv_bij_on_src_I}$}
  Since it is both injective on the source set of particulars \<open>src.\<P>\<close> and 
  surjective onto the image of \<open>\<phi>\<close> (\<open>\<phi> ` src.\<P>\<close>), the morphism \<open>\<phi>\<close> is
  a bijection between \<open>src.\<P>\<close> and \<open>\<phi> ` src.\<P>\<close>:

  \[ @{thm phi_inv_bij_on_src_I} \]

  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_inv_morph_img:
  assumes \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close>
  shows \<open>\<phi> (\<phi>\<inverse> x) = x\<close>
  using assms f_Inv_eq[of x \<phi> src.\<P>] morph_image_def 
  by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name morph_inv_morph_img}$}
  Since it's surjective on \<open>\<phi>\<close>'s image, the inverse morphism is a right-inverse for
  the \<open>\<phi>\<close>'s image:

  \[ @{thm morph_inv_morph_img} \]

  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_inheres_in_reflects_on_image[simp]:
  assumes \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close> \<open>y \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close> 
  shows  \<open>x \<triangleleft>\<^sub>t y \<longleftrightarrow> \<phi>\<inverse> x \<triangleleft>\<^sub>s \<phi>\<inverse> y\<close>
proof -
  obtain A: \<open>\<phi>\<inverse> x \<in> src.\<P>\<close>  \<open>\<phi>\<inverse> y \<in> src.\<P>\<close>
    using phi_inv_scope assms by blast
  obtain B[simp]: \<open>\<phi> (\<phi>\<inverse> x) = x\<close> \<open>\<phi> (\<phi>\<inverse> y) = y\<close>
    using assms morph_inv_morph_img by simp
  have C[simp]: \<open>(\<exists>y'. \<phi>\<inverse> x \<triangleleft>\<^sub>s y' \<and> y = \<phi> y') \<longleftrightarrow> \<phi>\<inverse> x \<triangleleft>\<^sub>s \<phi>\<inverse> y\<close>
    by (metis B(2) inv_morph_morph src.inherence_scope)
  show \<open>?thesis\<close>    
    using morph_reflects_inherence[of \<open>\<phi>\<inverse> x\<close> \<open>\<phi>\<inverse> y\<close>] A B C by metis
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name inv_inheres_in_reflects_on_image}$}
  The inverse of an injective morphism function reflects the inherence relation, i.e.
  for any \<open>x\<close> and \<open>y\<close> in the image of \<open>\<phi>\<close>, \<open>x\<close> inheres in \<open>y\<close> if and only if
  their respective inverses also stand in the same relation:
  \[ @{thm inv_inheres_in_reflects_on_image } \]
  \end{lemma}
\<close>


lemma \<^marker>\<open>tag (proof) aponly\<close> inv_towardness_reflects_on_image[simp]:
  assumes \<open>x \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close> \<open>y \<in> \<P>\<^sub>i\<^sub>m\<^sub>g\<close> 
  shows  \<open>x \<longlongrightarrow>\<^sub>t y \<longleftrightarrow> \<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> y\<close>
proof -
  obtain A: \<open>\<phi>\<inverse> x \<in> src.\<P>\<close>  \<open>\<phi>\<inverse> y \<in> src.\<P>\<close>
    using phi_inv_scope assms by blast
  obtain B[simp]: \<open>\<phi> (\<phi>\<inverse> x) = x\<close> \<open>\<phi> (\<phi>\<inverse> y) = y\<close>
    using assms  morph_inv_morph_img morph_image_def by simp
  have C[simp]: \<open>(\<exists>z. \<phi>\<inverse> x \<longlongrightarrow>\<^sub>s z \<and> y = \<phi> z) \<longleftrightarrow> \<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> y\<close>
  proof
    assume \<open>\<exists>z. \<phi>\<inverse> x \<longlongrightarrow>\<^sub>s z \<and> y = \<phi> z\<close>
    then obtain z where z: \<open>\<phi>\<inverse> x \<longlongrightarrow>\<^sub>s z\<close> \<open>y = \<phi> z\<close> by blast
    have \<open>z \<in> src.\<P>\<close> using src.towardness_scope z(1) by blast
    then have \<open>\<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> (\<phi> z)\<close>
      using inv_morph_morph z(1) by metis
    then show \<open>\<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> y\<close> using z(2) by simp
  next
    assume as: \<open>\<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> y\<close>
    show \<open>\<exists>z. \<phi>\<inverse> x \<longlongrightarrow>\<^sub>s z \<and> y = \<phi> z\<close>
      apply (intro exI[of _ \<open>\<phi>\<inverse> y\<close>] conjI as)
      using morph_inv_morph_img assms(2) by simp
  qed
  then show \<open>?thesis\<close>
    using morph_reflects_towardness A(1) morph_inv_morph_img assms(1)     
    by (metis A(2) B(2))    
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name inv_towardness_reflects_on_image}$}
  Similarly, the inverse of an injective morphism also reflects the 
  towardness relation, i.e. for any \<open>x\<close> and \<open>y\<close> in the image of \<open>\<phi>\<close>, 
  \<open>x\<close> os directed towards \<open>y\<close> if and only if
  their respective inverses also stand in the same relation:
  \[ @{thm inv_towardness_reflects_on_image } \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> world_preserve_inv_img:
  assumes \<open>w\<^sub>t \<in> tgt.\<W>\<close>
  shows \<open>\<phi>\<inverse> ` (w\<^sub>t \<inter> \<P>\<^sub>i\<^sub>m\<^sub>g) \<in> src.\<W>\<close>  
proof -
  obtain w\<^sub>s where A: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close>
    using morph_worlds_correspond_tgt_src[OF assms] by blast 
  obtain B: \<open>w\<^sub>s \<in> src.\<W>\<close> 
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
    using world_corresp_E[OF A] by metis
  have C: \<open>\<phi>\<inverse> ` (w\<^sub>t \<inter> \<P>\<^sub>i\<^sub>m\<^sub>g) = w\<^sub>s\<close>
    apply (intro set_eqI ; simp add: image_iff B Bex_def ; intro iffI ; (elim exE conjE)? ; hypsubst? ; simp?)
    subgoal for z
      using B(2) by blast
    subgoal premises P for z
      apply (rule exI[of _ \<open>\<phi> z\<close>] ; intro conjI exI[of _ \<open>z\<close>])
      subgoal G1 using B P by blast
      subgoal G2 using B P by blast
      subgoal G3 using B P by blast
      using B P G1 G2 G3 by auto
    done
  then show \<open>?thesis\<close>
    using B(1) by simp
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
 \begin{lemma}{$@{thm_name world_preserve_inv_img}$}
  Given an injective morphism, it is possible to determine some of its
  source possible worlds from its target possible worlds, using the 
  following lemma:  
  \[ @{thm world_preserve_inv_img } \]
  \end{lemma}
\<close>

end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> particular_struct_surjection
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  A morphism function that is a surjection onto the set of particulars of its
  target structure is characterized by the fact that its image corresponds to
  the set of particulars of the target structure and by the fact that the morphism
  function has a right-inverse function, as per the following lemmas:  
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> I_img_eq_tgt_I[simp]: \<open>\<P>\<^sub>i\<^sub>m\<^sub>g = tgt.\<P>\<close>
  by (simp only: morph_image_def morph_is_surjective)

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name I_img_eq_tgt_I}$}
The image of surjective morphism function is equivalent to the set of particulars if the
target structure:
\[ @{thm I_img_eq_tgt_I} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_morph[simp]:
  assumes \<open>x \<in> tgt.\<P>\<close>
  shows \<open>\<phi> (\<phi>\<inverse> x) = x\<close>
  using assms by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name inv_morph_morph}$}
For any surjective morphism, there is at least one function that serves as its right-inverse:
\[ @{thm inv_morph_morph }  \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> world_preserve_img[intro!]:
  assumes \<open>w\<^sub>s \<in> src.\<W>\<close>
  shows \<open>\<phi> ` w\<^sub>s \<in> tgt.\<W>\<close>    
proof -
  obtain w\<^sub>t where A: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close>
    using morph_worlds_correspond_src_tgt[OF assms] by blast 
  obtain B: \<open>w\<^sub>t \<in> tgt.\<W>\<close> 
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
    using world_corresp_E[OF A] by metis  
  have C: \<open>\<phi> ` w\<^sub>s = w\<^sub>t\<close>
    apply (intro set_eqI ; simp add: image_iff B Bex_def ; intro iffI ; (elim exE conjE)? ; hypsubst? ; simp?)
    subgoal G1 for z
      using B(2) assms by blast
    subgoal premises P for z
      apply (rule exI[of _ \<open>\<phi>\<inverse> z\<close>])      
      by (metis Inv_def P B inv_into_into inv_morph_morph 
                morph_is_surjective tgt.\<P>_I)      
    done
  then show \<open>?thesis\<close>
    using B(1) by simp
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
 \begin{lemma}{$@{thm_name world_preserve_img}$}
  Given a surjective morphism, it is possible to determine some of its
  target possible worlds from its source possible worlds, using the 
  following lemma:  
  \[ @{thm world_preserve_img } \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_quality_spaces_eq_src[simp]: \<open>tgt.\<Q>\<S> = src.\<Q>\<S>\<close>   
proof (rule ; (intro quality_space_subset subsetI)?)  
  fix Q
  assume \<open>Q \<in> tgt.\<Q>\<S>\<close>
  then obtain x q where A: \<open>x \<leadsto>\<^sub>t q\<close> \<open>q \<in> Q\<close> 
    using tgt.every_quality_space_is_used by blast
  then obtain B: \<open>x \<in> tgt.\<P>\<close> \<open>x \<in> tgt.\<M>\<close>
    using tgt.assoc_quale_scopeD by blast
  then obtain w\<^sub>t where C: \<open>w\<^sub>t \<in> tgt.\<W>\<close> \<open>x \<in> w\<^sub>t\<close>
    by blast
  then obtain w\<^sub>s where C1: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> 
    using morph_worlds_correspond_tgt_src by fastforce
  then obtain w\<^sub>s where D: \<open>w\<^sub>s \<in> src.\<W>\<close>
    \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s\<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
    using world_corresp_E[OF C1] B by metis
  obtain y where \<open>x = \<phi> y\<close> \<open>y \<in> src.\<P>\<close> 
    using morph_is_surjective B(1) by blast
  then have \<open>y \<leadsto>\<^sub>s q\<close> using A(1) morph_reflects_quale_assoc by blast
  then show \<open>Q \<in> src.\<Q>\<S>\<close> 
    using A(2) quality_space_subset 
    by (smt \<open>Q \<in> tgt.\<Q>\<S>\<close> quality_space.qspace_eq_I src.\<Q>_E src.assoc_quale_scopeD(2) subsetD tgt.quality_space_axioms)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name tgt_quality_spaces_eq_src}$}
In a surjective morphism, the set of quality spaces of the source and target structures are 
equivalent:
\[ @{thm tgt_quality_spaces_eq_src }  \]
\end{lemma}
\<close>

end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> particular_struct_bijection
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_bijective[intro!,simp]: \<open>bij_betw \<phi> src.\<P> tgt.\<P>\<close>  
  using morph_bij_on_img by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name morph_bijective}$:w}
  Since the morphism function is both injective and surjective, it is also
  bijective:
 \[ @{thm morph_bijective} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_bijective[intro!,simp]: \<open>bij_betw \<phi>\<inverse> tgt.\<P> src.\<P>\<close>  
  using phi_inv_bij_on_src_I by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name inv_morph_bijective}$}
  The inverse of a bijection is also a bijection:
 \[ @{thm inv_morph_bijective} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_injective[intro!,simp]: \<open>inj_on \<phi>\<inverse> tgt.\<P>\<close>
  using phi_inv_inj_on_I_img I_img_eq_tgt_I by simp

declare \<^marker>\<open>tag (proof) aponly\<close>
     inv_towardness_reflects_on_image[simp del]
     inv_inheres_in_reflects_on_image[simp del]

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The bijective nature of the morphism function entails the following reflection
  lemmas, which mirror the reflection axioms defined at @{locale pre_particular_struct_morphism}:
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_inheres_in_reflects[simp]:
  assumes \<open>x \<in> tgt.\<P>\<close> \<open>y \<in> tgt.\<P>\<close> 
  shows  \<open>\<phi>\<inverse> x \<triangleleft>\<^sub>s \<phi>\<inverse> y \<longleftrightarrow> x \<triangleleft>\<^sub>t y\<close>
  using inv_inheres_in_reflects_on_image assms by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name inv_inheres_in_reflects}$}
  The morphism function inverse reflects inherence related endurants from the
  target structure back into the source structure:
 \[ @{thm inv_inheres_in_reflects} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_towardness_reflects[simp]:
  assumes \<open>x \<in> tgt.\<P>\<close> \<open>y \<in> tgt.\<P>\<close> 
  shows  \<open>\<phi>\<inverse> x \<longlongrightarrow>\<^sub>s \<phi>\<inverse> y \<longleftrightarrow> x \<longlongrightarrow>\<^sub>t y\<close>
  using assms inv_towardness_reflects_on_image 
  by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name inv_towardness_reflects}$}
  Similarly, the morphism function inverse reflects towardness relata from the
  target structure back into the source structure:
 \[ @{thm inv_towardness_reflects} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_assoc_quale_reflects[simp]:
  assumes \<open>x \<in> tgt.\<P>\<close> \<open>y \<in> tgt.\<P>\<close> 
  shows  \<open>\<phi>\<inverse> x \<leadsto>\<^sub>s q \<longleftrightarrow> x \<leadsto>\<^sub>t q\<close>
  using assms 
  by (simp add: phi_inv_scope)

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name inv_assoc_quale_reflects}$}
  The quale association relation is also reflected back into the source structure:
 \[ @{thm inv_assoc_quale_reflects} \]
\end{lemma}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  If there is a bijection between two particular structures, their possible world
  sets present several useful symmetries, as shown in the following lemmas:
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> world_preserve_inv_img1[intro!]:
  assumes \<open>w\<^sub>t \<in> tgt.\<W>\<close>
  shows \<open>\<phi>\<inverse> ` w\<^sub>t \<in> src.\<W>\<close>
  using assms world_preserve_inv_img assms 
  by (metis I_img_eq_tgt_I inf.orderE tgt.worlds_are_made_of_particulars)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This is a refined version of the @{thm_name world_preserve_inv_img} 
  (introduced in @{locale particular_struct_injection}):

  \begin{lemma}{$@{thm_name world_preserve_inv_img1}$}
  The image of a possible world of the target structure under the
  inverse of the morphism function is also a possible world in the
  source structure:
  \[ @{thm world_preserve_inv_img1} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_phi_inv_world[simp]: 
  assumes \<open>w \<in> tgt.\<W>\<close>
  shows \<open>\<phi> ` \<phi>\<inverse> ` w = w\<close>  
  by (simp add: assms image_Inv_cancel
          possible_worlds.worlds_are_made_of_particulars 
          tgt.possible_worlds_axioms)
  
text \<^marker>\<open>tag bodyonly\<close> \<open> 
  \begin{lemma}{$@{thm_name phi_phi_inv_world}$}
  The image of the inverse function is a right-inverse of the image of the morphism function
  with respect to the set of possible in worlds in the target structure:
  \[ @{thm phi_phi_inv_world} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_inv_phi_world[simp]: 
  assumes \<open>w \<in> src.\<W>\<close>
  shows \<open>\<phi>\<inverse> ` \<phi> ` w = w\<close>
proof -
  have \<open>x \<in> w \<Longrightarrow> x \<in> src.\<P>\<close> for x using assms by blast
  then have \<open>\<phi>\<inverse> (\<phi> x) = x\<close> if \<open>x \<in> w\<close> for x by (simp add: that)
  then show \<open>?thesis\<close>    
    using src.worlds_are_made_of_particulars    
    by (metis assms inv_into_image_cancel morph_is_injective 
         phi_phi_inv_world world_preserve_img world_preserve_inv_img1) 
qed

text \<^marker>\<open>tag bodyonly\<close> \<open> 
  \begin{lemma}{$@{thm_name phi_inv_phi_world}$}
  Similarly, the image of the inverse function is a left-inverse of the image of the morphism function
  with respect to the set of possible in worlds in the source structure:
  \[ @{thm phi_inv_phi_world} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> src_world_corresp_unique:
  assumes \<open>w \<Leftrightarrow> w\<^sub>1\<close> \<open>w \<Leftrightarrow> w\<^sub>2\<close>
  shows \<open>w\<^sub>1 = w\<^sub>2\<close>
proof -
  obtain A: \<open>w \<in> src.\<W>\<close> \<open>w\<^sub>1 \<in> tgt.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w \<longleftrightarrow> \<phi> x \<in> w\<^sub>1\<close>
    using assms(1) world_corresp_E by blast
  obtain B: \<open>w\<^sub>2 \<in> tgt.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w \<longleftrightarrow> \<phi> x \<in> w\<^sub>2\<close>
    using assms(2) world_corresp_E by blast
  obtain C: \<open>\<forall>x. x \<in> src.\<P> \<longrightarrow> (\<phi> x \<in> w\<^sub>1 \<longleftrightarrow> \<phi> x \<in> w\<^sub>2)\<close>
            \<open>\<forall>x. x \<in> src.\<P> \<longrightarrow> (\<phi> x \<in> w\<^sub>2 \<longleftrightarrow> \<phi> x \<in> w\<^sub>1)\<close>
    using A B by metis
  have D: \<open>x \<in> w\<^sub>1\<close> if as: \<open>w\<^sub>1 \<in> tgt.\<W>\<close> \<open>w\<^sub>2 \<in> tgt.\<W>\<close> \<open>\<forall>x. x \<in> src.\<P> \<longrightarrow> (\<phi> x \<in> w\<^sub>1 \<longleftrightarrow> \<phi> x \<in> w\<^sub>2)\<close> \<open>x \<in> w\<^sub>2\<close> for x w\<^sub>1 w\<^sub>2
  proof -
    have \<open>x \<in> tgt.\<P>\<close> using as by blast 
    then obtain y where BB: \<open>x = \<phi> y\<close> \<open>y \<in> src.\<P>\<close> 
      using I_img_eq_tgt_I by blast
    then show \<open>?thesis\<close> using BB as by metis
  qed        
  show \<open>?thesis\<close>
    using D[OF A(2) B(1) C(1)] D[OF B(1) A(2) C(2)] by blast
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name src_world_corresp_unique}$}
For every possible world in the source structure, there is a unique
correspondent possible world in the target structure:
\[ @{thm src_world_corresp_unique} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_world_corresp_unique:
  assumes \<open>w\<^sub>1 \<Leftrightarrow> w\<close> \<open>w\<^sub>2 \<Leftrightarrow> w\<close>
  shows \<open>w\<^sub>1 = w\<^sub>2\<close>
proof -
  obtain A: \<open>w \<in> tgt.\<W>\<close> \<open>w\<^sub>1 \<in> src.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>1 \<longleftrightarrow> \<phi> x \<in> w\<close>
    using assms(1) world_corresp_E by blast
  obtain B: \<open>w\<^sub>2 \<in> src.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>2 \<longleftrightarrow> \<phi> x \<in> w\<close>  
    using assms(2) world_corresp_E by blast
  obtain C: \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>1 \<longleftrightarrow> x \<in> w\<^sub>2\<close>           
    using A B by metis
  then have D: \<open>\<And>x. x \<in> w\<^sub>1 \<longleftrightarrow> x \<in> w\<^sub>2\<close>           
    using A(2) B(1) src.worlds_are_made_of_particulars by blast
  then show \<open>?thesis\<close>
    by auto
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{lemma}{$@{thm_name tgt_world_corresp_unique}$}
Conversely, for every possible world in the target structure, there is a unique
correspondent possible world in the source structure:
\[ @{thm tgt_world_corresp_unique} \]
\end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> src_world_corresp_image:
  assumes \<open>w \<in> src.\<W>\<close>
  shows \<open>w \<Leftrightarrow> \<phi> ` w\<close>
proof -
  obtain w\<^sub>t where A: \<open>w \<Leftrightarrow> w\<^sub>t\<close> 
    using morph_worlds_correspond_src_tgt assms
    by fastforce
  then obtain B: \<open>w\<^sub>t \<in> tgt.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>   
    using world_corresp_E by metis
  obtain C: \<open>x \<in> w \<Longrightarrow> x \<in> src.\<P>\<close> for x using assms 
    by (simp add: src.\<P>_I)
  obtain D: \<open>x \<in> w\<^sub>t \<Longrightarrow> x \<in> tgt.\<P>\<close> for x using B(1)
    by auto
  have E: \<open>\<phi> ` w = w\<^sub>t\<close>
  proof (intro set_eqI iffI ; (elim imageE)? ; simp add: image_def Bex_def ; hypsubst_thin?)
    show G1: \<open>\<phi> x \<in> w\<^sub>t\<close> if \<open>x \<in> w\<close> for x
      using B(2) C that by metis      
    show \<open>\<exists>y. y \<in> w \<and> x = \<phi> y\<close> if \<open>x \<in> w\<^sub>t\<close> for x
      supply x_in_tgt_I[simp,intro!] = D[OF that]
      supply phi_phi_inv[simp] = inv_morph_morph[OF x_in_tgt_I]
      apply (intro exI[of _ \<open>\<phi>\<inverse> x\<close>] conjI ; simp?)
      apply (intro B(2)[of \<open>\<phi>\<inverse> x\<close>,simplified,THEN iffD2] that)      
      by (simp add: phi_inv_scope)
  qed
  then show \<open>?thesis\<close>
    using A B by simp
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_world_corresp_inv_image[intro!]:
  assumes \<^marker>\<open>tag (proof) aponly\<close> \<open>w \<in> tgt.\<W>\<close>
  shows \<open>\<phi>\<inverse> ` w \<Leftrightarrow> w\<close>
proof -
  obtain w\<^sub>s where A: \<open>w\<^sub>s \<Leftrightarrow> w\<close> 
    using morph_worlds_correspond_tgt_src assms
    by fastforce
  then obtain B: \<open>w\<^sub>s \<in> src.\<W>\<close> 
      \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<close>
    using world_corresp_E by metis
  obtain C: \<open>x \<in> w\<^sub>s \<Longrightarrow> x \<in> src.\<P>\<close> for x using assms     
    using B(1) by blast
  obtain D: \<open>x \<in> w \<Longrightarrow> x \<in> tgt.\<P>\<close> for x using assms
    by auto
  have E: \<open>\<phi>\<inverse> ` w = w\<^sub>s\<close>
  proof (intro set_eqI iffI ; (elim imageE)? ; simp add: image_def Bex_def ; hypsubst_thin?)
    show G1: \<open>\<phi>\<inverse> x \<in> w\<^sub>s\<close> if \<open>x \<in> w\<close> for x      
      using B(2) assms phi_inv_scope tgt.\<P>_I that by auto      
    show \<open>\<exists>y. y \<in> w \<and> x = \<phi>\<inverse> y\<close> if \<open>x \<in> w\<^sub>s\<close> for x
      apply (intro exI[of _ \<open>\<phi> x\<close>] conjI) 
      subgoal G1 using A that by blast
      subgoal using that C by auto
      done
  qed
  then show \<open>?thesis\<close>
    using A B by simp
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> src_world_corresp_image_iff:
  assumes \<open>w \<in> src.\<W>\<close>
  shows \<open>w \<Leftrightarrow> w' \<longleftrightarrow> w' = \<phi> ` w\<close>
  by (meson assms src_world_corresp_image src_world_corresp_unique)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name src_world_corresp_image_iff}$}
  In fact, the only possible world of the target structure that corresponds 
  to a given possible world of the source structure is exactly the image of
  the source possible world:
  \[ @{thm src_world_corresp_image_iff} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_world_corresp_inv_image_iff:
  assumes \<open>w \<in> tgt.\<W>\<close>
  shows \<open>w' \<Leftrightarrow> w \<longleftrightarrow> w' = \<phi>\<inverse> ` w\<close>
  by (meson assms tgt_world_corresp_inv_image tgt_world_corresp_unique)

lemma tgt_substantials_eq_img: \<open>tgt.\<S> = \<phi> ` src.\<S>\<close>
  apply auto
  by (metis I_img_eq_tgt_I image_eqI inv_morph_morph 
       morph_preserves_moments phi_inv_scope src.particular_cases_1)

lemma tgt_moments_eq_img: \<open>tgt.\<M> = \<phi> ` src.\<M>\<close>
  apply auto
  by (metis imageI morph_image_E morph_is_surjective
          morph_preserves_moments_simp particular_struct_morphism_sig.morph_image_def 
          tgt.\<M>_E tgt.inherence_scope)  

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name tgt_world_corresp_inv_image_iff}$}
  Conversely, the only possible world of the source structure that corresponds 
  to a given possible world of the target structure is exactly the inverse image of
  the target possible world:
  \[ @{thm tgt_world_corresp_inv_image_iff} \]
  \end{lemma}
\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_is_bijective_morphism[simp,intro!]: \<open>particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 (\<phi>\<inverse>)\<close>
proof -    
  note AA = Inv_scope'[of \<phi> \<open>src.\<P>\<close>,simplified]
  interpret I: pre_particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>\<phi>\<inverse>\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales)
    subgoal G1
      by (auto simp add: tgt_substantials_eq_img)
    subgoal G2
      apply (simp add: tgt_moments_eq_img ; intro AA)
      by auto
    subgoal G3
      using Inv_extensional[of \<open>src.\<P>\<close> \<phi>] morph_is_surjective
      by simp
    subgoal G4 by (simp add: phi_inv_scope)
    subgoal G5 by (metis inv_inheres_in_reflects)    
    subgoal G6 using phi_inv_img by auto
    subgoal G7 by blast
    by simp          

  interpret I: particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>\<phi>\<inverse>\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales)
    subgoal morph_worlds_correspond_src_tgt for w\<^sub>t 
      apply (intro exI[of _ \<open>\<phi>\<inverse> ` w\<^sub>t\<close>] ; simp ; intro particular_struct_morphism_sig.world_corresp_I ; simp?)
      subgoal G3_1 by blast
      subgoal G3_2 by (metis image_eqI inv_morph_morph phi_phi_inv_world)      
      done
    subgoal morph_worlds_correspond_tgt_src for w\<^sub>s
      apply (intro exI[of _ \<open>\<phi> ` w\<^sub>s\<close>] ; simp ; intro particular_struct_morphism_sig.world_corresp_I ; simp?)
      subgoal G3_1 by blast
      subgoal G3_2 by (metis image_eqI morph_inv_morph_img phi_inv_phi_world I_img_eq_tgt_I)      
      done
    done

  interpret I: particular_struct_injection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>\<phi>\<inverse>\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
    by (unfold_locales ; simp)

  interpret I: particular_struct_surjection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>\<phi>\<inverse>\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales ; simp)    
    using phi_inv_img by auto

  show ?thesis    
    by (unfold_locales)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}{$@{thm_name inv_is_bijective_morphism}$}
  Finally, we have that the inverse function of a bijective morphism function is also a 
  morphism. More specifically, it is also a bijective morphism:
  \[ @{thm inv_is_bijective_morphism} \]
  \end{lemma}
\<close>

end \<^marker>\<open>tag aponly\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_inj_comp[intro]:
  assumes 
    \<open>\<phi>\<^sub>1 \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
    \<open>\<phi>\<^sub>2 \<in> Morphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub>\<close>
    \<open>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1 \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>
  shows \<open>\<phi>\<^sub>1 \<in> InjMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>  
proof -
  interpret phi1: particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1
    using assms(1) by simp
  interpret phi2: particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2
    using assms(2) by simp
  interpret phi21: particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 \<open>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1\<close>
    using assms(3) by simp  
  have \<open>inj_on \<phi>\<^sub>1 phi1.src.\<P>\<close>
    using phi21.morph_is_injective inj_on_map_comp_imageI2 by blast
  then show ?thesis
    by (simp ; unfold_locales ; simp)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_surj_comp[intro]:
  assumes 
    \<open>\<phi>\<^sub>1 \<in> Morphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2\<^esub>\<close>
    \<open>\<phi>\<^sub>2 \<in> Morphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub>\<close>
    \<open>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1 \<in> BijMorphs\<^bsub>\<Gamma>\<^sub>1,\<Gamma>\<^sub>3\<^esub>\<close>
  shows \<open>\<phi>\<^sub>2 \<in> SurjMorphs\<^bsub>\<Gamma>\<^sub>2,\<Gamma>\<^sub>3\<^esub>\<close>  
proof -
  interpret phi1: particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1
    using assms(1) by simp
  interpret phi2: particular_struct_morphism \<Gamma>\<^sub>2 \<Gamma>\<^sub>3 \<phi>\<^sub>2
    using assms(2) by simp
  interpret phi21: particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>3 \<open>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1\<close>
    using assms(3) by simp    
  have \<open>phi2.tgt.\<P> \<subseteq> \<phi>\<^sub>2 ` phi2.src.\<P>\<close>
    apply (simp add: image_def Bex_def ; safe)
    subgoal for x      
      using [[show_sorts]]
      using exI[of _ \<open>invMorph \<Gamma>\<^sub>1 (\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) x\<close>]
    using phi21.morph_is_surjective 
    by (metis (mono_tags, lifting) compose_eq phi1.morph_preserves_particulars 
          phi21.inv_morph_morph phi21.morph_image_def phi21.phi_inv_scope)
    done
  then show ?thesis
    apply (simp ;  unfold_locales)
    by blast
qed

subsection \<^marker>\<open>tag aponly\<close> \<open>Morphism image structure\<close> 

abbreviation \<^marker>\<open>tag aponly\<close> lift_morph_1  where
  \<open>lift_morph_1 \<Gamma> \<phi> p x \<equiv> \<exists>y. p \<Gamma> y \<and> x = \<phi> y\<close>

abbreviation \<^marker>\<open>tag aponly\<close> lift_morph_2 where
  \<open>lift_morph_2 \<Gamma> \<phi> p x y \<equiv> \<exists>x\<^sub>1 y\<^sub>1. p \<Gamma> x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1\<close>

abbreviation \<^marker>\<open>tag aponly\<close> lift_morph_2_1 ::
  \<open>('p\<^sub>1,'a) particular_struct \<Rightarrow>
   ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow>
   (('p\<^sub>1,'a) particular_struct \<Rightarrow> 'p\<^sub>1 \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
   'p\<^sub>2 \<Rightarrow>
   'b \<Rightarrow>
   bool\<close> where
  \<open>lift_morph_2_1 \<Gamma> \<phi> p x z \<equiv> lift_morph_1 \<Gamma> \<phi> (\<lambda>\<Gamma> x. p \<Gamma> x z) x\<close>

definition \<^marker>\<open>tag aponly\<close> MorphImg :: \<open>('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> ('p\<^sub>1,'q) particular_struct \<Rightarrow> ('p\<^sub>2,'q) particular_struct\<close>  
  where \<open>MorphImg \<phi> \<Gamma> \<equiv>
  \<lparr>
    ps_quality_spaces = ps_quality_spaces \<Gamma>,
    ps_worlds = ((`) \<phi>) ` ps_worlds \<Gamma>,
    ps_inheres_in = lift_morph_2 \<Gamma> \<phi> ps_inheres_in,
    ps_assoc_quale = lift_morph_2_1 \<Gamma> \<phi> ps_assoc_quale,
    ps_towards = lift_morph_2 \<Gamma> \<phi> ps_towards
  \<rparr>\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_morphism_image_simps[simp]:
  \<open>ps_quality_spaces (MorphImg \<phi> \<Gamma>) =
    ps_quality_spaces \<Gamma>\<close>
  \<open>ps_worlds (MorphImg \<phi> \<Gamma>) =
    { \<phi> ` w | w . w \<in> ps_worlds \<Gamma> }\<close>
  \<open>ps_inheres_in (MorphImg \<phi> \<Gamma>) =
     (\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. ps_inheres_in \<Gamma> x\<^sub>1 y\<^sub>1 
          \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close>
  \<open>ps_assoc_quale (MorphImg \<phi> \<Gamma>) =
     (\<lambda>x q. \<exists>x\<^sub>1. ps_assoc_quale \<Gamma> x\<^sub>1 q 
          \<and> x = \<phi> x\<^sub>1)\<close>
  \<open>ps_towards (MorphImg \<phi> \<Gamma>) =
    (\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. ps_towards \<Gamma> x\<^sub>1 y\<^sub>1 
          \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close>
  by (auto simp: MorphImg_def)


context particular_struct_bijection
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_is_morph_img: \<open>MorphImg \<phi> \<Gamma>\<^sub>1 = \<Gamma>\<^sub>2\<close> 
proof (rule sym)
  show \<open>\<Gamma>\<^sub>2 = MorphImg \<phi> \<Gamma>\<^sub>1\<close>  
    apply (auto ; (intro ext iffI conjI)? ; (elim conjE exE)?)
    subgoal G1 using phi_phi_inv_world by blast
    subgoal G2 by (metis inv_inheres_in_reflects inv_morph_morph tgt.inherence_scope)
    subgoal G3 using src.inherence_scope by auto
    subgoal G4 by (metis I_img_eq_tgt_I inv_morph_morph morph_reflects_quale_assoc particular_struct_injection.phi_inv_scope particular_struct_injection_axioms tgt.assoc_quale_scopeD(1))
    subgoal G5 using morph_reflects_quale_assoc src.assoc_quale_scopeD(1) by blast    
    subgoal G6 by (metis inv_towardness_reflects_on_image morph_inv_morph_img particular_struct_surjection.I_img_eq_tgt_I particular_struct_surjection_axioms tgt.towardness_scopeE)
    using morph_reflects_towardness by blast
qed

declare particular_struct_morphism_image_simps[simp del]

end

context particular_struct_permutation
begin                  

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_img_phi_eq_itself[simp]: \<open>MorphImg \<phi> \<Gamma> = \<Gamma>\<close>
  apply (intro particular_struct_eqI
        ; simp only: particular_struct_morphism_image_simps
        ; (intro ext)?
        ; auto?)
  subgoal G1 using phi_phi_inv_world by blast
  subgoal G2 for x y 
    by (metis inherence_scope inv_inheres_in_reflects inv_morph_morph)
  subgoal G3 using assoc_quale_scopeD(1) morph_reflects_quale_assoc by blast
  subgoal G4 by (metis particular_struct_morphism_image_simps(4)
                  tgt_is_morph_img)
  subgoal G5 using morph_reflects_towardness by blast 
  by (metis I_img_eq_tgt_I inv_towardness_reflects 
      morph_inv_morph_img towardness_scopeD(2) towardness_scopeD(3))

end


lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphism_tgt_unique:
  fixes
    \<Gamma> :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes 
    \<open>particular_struct_bijection \<Gamma> \<Gamma>\<^sub>1 \<phi>\<close>
    \<open>particular_struct_bijection \<Gamma> \<Gamma>\<^sub>2 \<phi>\<close>
  shows \<open>\<Gamma>\<^sub>1 = \<Gamma>\<^sub>2\<close>
  using
    assms[THEN particular_struct_bijection.tgt_is_morph_img]
  by simp

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphism_iff_isomorphism_to_morphimg:
  \<open>particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<longleftrightarrow>
    particular_struct_bijection \<Gamma>\<^sub>1 (MorphImg \<phi> \<Gamma>\<^sub>1) \<phi> \<and>
    \<Gamma>\<^sub>2 =  MorphImg \<phi> \<Gamma>\<^sub>1\<close>   
  using particular_struct_bijection.tgt_is_morph_img by blast

locale particular_struct_bijection_1 =
    particular_struct_injection where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<^sub>1\<close> 
          and \<phi> = \<open>\<phi>\<close> and \<Gamma>\<^sub>2 = \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> 
          and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> + 
    particular_struct_surjection where \<Gamma>\<^sub>1 = \<open>\<Gamma>\<^sub>1\<close> 
          and \<phi> = \<open>\<phi>\<close> and \<Gamma>\<^sub>2 = \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> 
          and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>
  for 
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<phi> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> and
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>       

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_bijection_iff_particular_struct_bijection_1:
  fixes
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
    \<phi> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>
  shows
    \<open>particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<longleftrightarrow>
      particular_struct_bijection_1 \<Gamma>\<^sub>1 \<phi> \<and>
      \<Gamma>\<^sub>2 = MorphImg \<phi> \<Gamma>\<^sub>1\<close>  
  using particular_struct_bijection.tgt_is_morph_img 
        particular_struct_bijection_1_def particular_struct_bijection_def 
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_bijection_iff_particular_struct_bijection_1_2:
  \<open>particular_struct_bijection_1 \<Gamma> \<phi> \<longleftrightarrow>
    particular_struct_bijection \<Gamma> (MorphImg \<phi> \<Gamma>) \<phi>\<close>
  supply R = 
    particular_struct_bijection_iff_particular_struct_bijection_1[
        of \<open>\<Gamma>\<close> \<open>MorphImg \<phi> \<Gamma>\<close> \<open>\<phi>\<close>]
  supply P = R[THEN iffD1,THEN conjunct1] R[THEN iffD2,simplified]
  using P by metis

sublocale \<^marker>\<open>tag aponly\<close> particular_struct_bijection_1 \<subseteq>
  particular_struct_bijection where  \<Gamma>\<^sub>1 = \<open>\<Gamma>\<^sub>1\<close> 
    and \<phi> = \<open>\<phi>\<close> and \<Gamma>\<^sub>2 = \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> 
    and Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>
  using particular_struct_bijection_iff_particular_struct_bijection_1
    particular_struct_bijection_1_axioms
  by metis
   
lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_bijection_1_comp:
  fixes
    \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
    \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close> and
    \<Gamma>\<^sub>3 :: \<open>('p\<^sub>3,'q) particular_struct\<close>
  assumes
    \<open>particular_struct_bijection_1 \<Gamma>\<^sub>1 \<phi>\<^sub>1\<^sub>2\<close>
    \<open>particular_struct_bijection_1 (MorphImg \<phi>\<^sub>1\<^sub>2 \<Gamma>\<^sub>1) \<phi>\<^sub>2\<^sub>3\<close>
  shows
    \<open>particular_struct_bijection_1 \<Gamma>\<^sub>1 (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1\<^sub>2)\<close>
  using assms
    particular_struct_bijection_comp
    particular_struct_bijection_iff_particular_struct_bijection_1
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> (in particular_struct_bijection) is_a_particular_struct_bijection_1: 
  \<open>particular_struct_bijection_1 \<Gamma>\<^sub>1 \<phi>\<close>
proof -  
  note tgt_is_morph_img[simp]
  interpret S: particular_struct \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close>        
    by (simp add: tgt.particular_struct_axioms)
  interpret M: particular_struct_injection \<Gamma>\<^sub>1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> \<phi>
    apply (simp)
    by (unfold_locales)
  show ?thesis
    by (unfold_locales ; simp)
qed

context particular_struct_permutation
begin                  

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_struct_permutation_to_isomorphism_1[intro,simp]: 
  \<open>particular_struct_bijection_1 \<Gamma> \<phi>\<close>
  apply (simp add: particular_struct_bijection_1_def ; intro conjI)  
  using particular_struct_injection_axioms particular_struct_surjection_axioms by auto          

end
  
definition \<^marker>\<open>tag aponly\<close> bijections1 :: \<open>('p,'q) particular_struct \<Rightarrow> 'p\<^sub>1 itself \<Rightarrow>  ('p \<Rightarrow> 'p\<^sub>1) set\<close> 
  (\<open>BijMorphs1\<^bsub>_,_\<^esub>\<close> [999] 1000)
  where \<open>BijMorphs1\<^bsub>\<Gamma>,_\<^esub> \<equiv> { \<phi> . particular_struct_bijection_1 \<Gamma> \<phi> }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_I[intro!]: 
  \<open>particular_struct_bijection_1 \<Gamma> \<phi> \<Longrightarrow> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close>
  by (auto simp: bijections1_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_D[dest!]: 
  \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> \<Longrightarrow> particular_struct_bijection_1 \<Gamma> \<phi>\<close>
  by (auto simp: bijections1_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections_iff[simp]: 
  \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> \<longleftrightarrow> particular_struct_bijection_1 \<Gamma> \<phi>\<close>
  by (auto simp: bijections1_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> bijections1_iff_bijections_to_morph_img: 
  \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> \<longleftrightarrow> \<phi> \<in> BijMorphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close>
  by (intro iffI ; 
      simp add: particular_struct_bijection_iff_particular_struct_bijection_1)
    
lemma \<^marker>\<open>tag (proof) aponly\<close> bijections1_are_morphisms: 
  \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> \<Longrightarrow> \<phi> \<in> Morphs\<^bsub>\<Gamma>, MorphImg \<phi> \<Gamma>\<^esub>\<close>  
  by (meson bijections1_iff_bijections_to_morph_img bijections_are_morphisms)

lemma \<^marker>\<open>tag (proof) aponly\<close> permutations_are_bijections1:  
  \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close>  
  by (simp add: 
      particular_struct_permutation.particular_struct_permutation_to_isomorphism_1)


definition \<^marker>\<open>tag aponly\<close> isomorphic_models
  :: \<open>('p,'q) particular_struct \<Rightarrow> 'p\<^sub>1 itself \<Rightarrow>
      ('p\<^sub>1,'q) particular_struct set\<close>
      (\<open>IsoModels\<^bsub>_,_\<^esub>\<close> [999,999] 1000) where
  \<open>IsoModels\<^bsub>\<Gamma>,X\<^esub> \<equiv> { MorphImg \<phi> \<Gamma> | \<phi> . \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_models_I[intro]:
  assumes \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close> \<open>\<Gamma>\<^sub>1 = MorphImg \<phi> \<Gamma>\<close>
  shows \<open>\<Gamma>\<^sub>1 \<in> IsoModels\<^bsub>\<Gamma>,X\<^esub>\<close>
  using assms
  by (auto simp: isomorphic_models_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_models_E[elim!]:
  assumes \<open>\<Gamma>\<^sub>1 \<in> IsoModels\<^bsub>\<Gamma>,X\<^esub>\<close>
  obtains \<phi> where \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close> \<open>\<Gamma>\<^sub>1 = MorphImg \<phi> \<Gamma>\<close>
  using assms
  by (auto simp: isomorphic_models_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_models_iff[simp]:
  \<open>\<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>,X\<^esub> \<longleftrightarrow> (\<exists>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>.  \<Gamma>' = MorphImg \<phi> \<Gamma>)\<close>
  by (auto simp: isomorphic_models_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_models_sym[sym]:
  assumes \<open>\<Gamma>\<^sub>1 \<in> IsoModels\<^bsub>\<Gamma>\<^sub>2,TYPE('p\<^sub>1)\<^esub>\<close>
  shows \<open>\<Gamma>\<^sub>2 \<in> IsoModels\<^bsub>\<Gamma>\<^sub>1,TYPE('p\<^sub>2)\<^esub>\<close>
  using assms
  by (metis isomorphic_models_iff bijections1_def mem_Collect_eq 
      particular_struct_bijection.inv_is_bijective_morphism 
      particular_struct_bijection_iff_particular_struct_bijection_1)

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> MorphImg_of_id[simp]: \<open>MorphImg id \<Gamma> = \<Gamma>\<close>  
  by (rule ; simp)

lemma morph_img_eq[simp]: \<open>MorphImg (id_on \<E>) \<Gamma> = \<Gamma>\<close>
  apply (simp only: MorphImg_def ; auto ; (intro ext iffI)?
         ; (elim exE conjE)? ; hypsubst_thin?)
  subgoal G1 by (simp add: Union_upper \<P>_def id_on_img)
  subgoal G2 by (simp add: Union_upper \<P>_def id_on_img)
  subgoal G3 by (simp add: inherence_scope)
  subgoal G4 by (metis id_on_eq(1) inherence_scope)
  subgoal G5 by (simp add: assoc_quale_scopeD(1))
  subgoal G6 by (metis assoc_quale_scopeD(1) id_on_eq(1))
  subgoal G7 by (simp add: towardness_scopeD(2) towardness_scopeD(3))    
  by (metis id_on_eq(1) towardness_scopeD(2) towardness_scopeD(3))


lemma \<^marker>\<open>tag (proof) aponly\<close> id_is_isomorphism[intro!,simp]: \<open>particular_struct_bijection_1 \<Gamma> (id_on (particulars \<Gamma>))\<close>
proof -
  have \<S>_subset[simp]: \<open>\<S> \<subseteq> \<E>\<close> by auto
  have \<M>_subset[simp]: \<open>\<M> \<subseteq> \<E>\<close> by auto
  have A: \<open>particular_struct_morphism \<Gamma> \<Gamma> (id_on (particulars \<Gamma>))\<close>
    apply (simp add: 
        particular_struct_bijection_1_def
        particular_struct_injection_def
        particular_struct_morphism_def
        pre_particular_struct_morphism_def
        particular_struct_surjection_def ; 
        intro conjI ; unfold_locales ; simp)
    subgoal by (rule id_on_extensional ; simp)
    subgoal by (rule id_on_extensional ; simp)      
    subgoal using towardness_scope by blast
    subgoal G1 for w
      by (intro exI[of _ \<open>w\<close>]
          particular_struct_morphism_sig.world_corresp_I ; simp)
    subgoal G2 for w
      by (intro exI[of _ \<open>w\<close>]
          particular_struct_morphism_sig.world_corresp_I ; simp)
    done
  then interpret particular_struct_morphism \<Gamma> \<Gamma> \<open>id_on (particulars \<Gamma>)\<close> .
  interpret P: particular_struct_morphism \<Gamma> \<Gamma> \<open>id_on \<E>\<close>
    using A by simp
  show ?thesis    
    by (simp add: particular_struct_bijection_1_def ; safe ; 
          unfold_locales ; simp)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> id_is_a_permutation[intro!,simp]: \<open>particular_struct_permutation \<Gamma> (id_on (particulars \<Gamma>))\<close>
proof -
  interpret id: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>id_on (particulars \<Gamma>)\<close>
    using id_is_isomorphism .
  show \<open>?thesis\<close>    
    apply (intro_locales ; simp?)
    subgoal 
      using id.src.id_is_a_morphism particular_struct_morphism.axioms(1)
            pre_particular_struct_morphism.axioms(3) 
      by fastforce
    subgoal 
      using id.src.id_is_a_morphism particular_struct_morphism_def 
      by auto
    subgoal 
      using id.particular_struct_injection_axioms particular_struct_injection_def by auto
    subgoal
      by (unfold_locales ; simp)
    done
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> id_is_an_injection[intro!,simp]: 
  \<open>particular_struct_injection \<Gamma> \<Gamma> (id_on (particulars \<Gamma>))\<close>
proof -
  interpret P: particular_struct_permutation \<Gamma> \<open>id_on (particulars \<Gamma>)\<close>
    by blast
  show ?thesis
    by intro_locales
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> id_in_isomorphs[intro!,simp]:
  fixes X  
  shows \<open>id_on (particulars \<Gamma>) \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close>
  by (intro bijections_I id_is_isomorphism)

lemma \<^marker>\<open>tag (proof) aponly\<close> itself_in_isomodels[intro!,simp]: 
  fixes X
  shows \<open>\<Gamma> \<in> IsoModels\<^bsub>\<Gamma>,X\<^esub>\<close>
  apply (intro isomorphic_models_I[of \<open>id_on (particulars \<Gamma>)\<close>] ; simp)  
  using \<Gamma>_simps(2) id_is_isomorphism by presburger
  

lemma \<^marker>\<open>tag (proof) aponly\<close> id_in_permutations[intro!,simp]: 
  \<open>id_on (particulars \<Gamma>) \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close>  
  by (intro permutations_I id_is_a_permutation)

end

context particular_struct_permutation
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_permutation[simp,intro!]: \<open>particular_struct_permutation \<Gamma> \<phi>\<inverse>\<close>
proof -
  interpret iso: particular_struct_bijection \<open>\<Gamma>\<close> \<open>\<Gamma>\<close> \<open>\<phi>\<inverse>\<close> by simp
  show \<open>?thesis\<close>
    by (intro_locales)
qed

end


context
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_in_BijMorphs[intro!,simp]: 
  \<open>invMorph \<Gamma> \<phi> \<in> BijMorphs1\<^bsub>MorphImg \<phi> \<Gamma>,X\<^esub>\<close> 
  if A: \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close>
proof -
  let \<open>?invmorph\<close> = \<open>invMorph \<Gamma>\<close>
  interpret phi: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
    using A by blast
  interpret inv: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<open>?invmorph \<phi>\<close>    
    using particular_struct_bijection_iff_particular_struct_bijection_1 by blast
  show \<open>?thesis\<close>    
    using inv.particular_struct_bijection_1_axioms 
    by blast    
qed  

lemma \<^marker>\<open>tag (proof) aponly\<close> inv_morph_in_Perms[intro!,simp]:  \<open>invMorph \<Gamma> \<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close> if A: \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close>
proof -
  let \<open>?invmorph\<close> = \<open>invMorph \<Gamma>\<close>
  interpret perm: particular_struct_permutation \<open>\<Gamma>\<close> \<open>\<phi>\<close> using A by simp
  
  interpret inv: particular_struct_permutation \<open>\<Gamma>\<close> \<open>?invmorph \<phi>\<close>
    by simp
  show \<open>?thesis\<close>
    by simp
qed  

end



lemma \<^marker>\<open>tag (proof) aponly\<close> (in particular_struct) morph_img_comp[simp]:   
  fixes \<phi>\<^sub>1 :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close> and
        \<phi>\<^sub>2 :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> 
  shows  \<open>MorphImg (\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) \<Gamma> = MorphImg \<phi>\<^sub>2 (MorphImg \<phi>\<^sub>1 \<Gamma>)\<close>
proof -

  interpret S4: particular_struct_sig \<open>MorphImg (\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1) \<Gamma>\<close> \<open>TYPE('p\<^sub>2)\<close> .   
  interpret S3: particular_struct_sig \<open>MorphImg \<phi>\<^sub>2 (MorphImg \<phi>\<^sub>1 \<Gamma>)\<close> \<open>TYPE('p\<^sub>2)\<close>.
  interpret S2: particular_struct_sig \<open>MorphImg \<phi>\<^sub>1 \<Gamma>\<close>  \<open>TYPE('p\<^sub>1)\<close>.
  
  have A: \<open>z \<in> particulars \<Gamma>\<close> if \<open>w \<in> \<W>\<close> \<open>z \<in> w\<close> for z w
    using that by (meson possible_worlds_sig.\<P>_I)

  have B: \<open>w \<subseteq> particulars \<Gamma>\<close> if \<open>w \<in> \<W>\<close> for w    
    using A that by blast

  have C[simp]: \<open>w \<in> \<W> \<Longrightarrow> (\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1) ` w =  \<phi>\<^sub>2 ` \<phi>\<^sub>1 ` w\<close>
    for w using  map_comp_img[OF B] by metis
  have D1[simp]: \<open>(\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) x = \<phi>\<^sub>2 (\<phi>\<^sub>1 x)\<close> if \<open>x \<triangleleft> y\<close> for x y
    using that by (meson compose_eq inherence_scope)
  have D2[simp]: \<open>(\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) x = \<phi>\<^sub>2 (\<phi>\<^sub>1 x)\<close> if \<open>y \<triangleleft> x\<close> for x y
    using that by (meson compose_eq inherence_scope)
  have E[simp]: \<open>(\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) x = \<phi>\<^sub>2 (\<phi>\<^sub>1 x)\<close> if \<open>x \<leadsto> q\<close> for x q
    apply (intro compose_eq)
    using that by (meson assoc_quale_scopeD(1)) 
  have F1[simp]: \<open>(\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) x = \<phi>\<^sub>2 (\<phi>\<^sub>1 x)\<close> if \<open>x \<longlongrightarrow> y\<close> for x y
    apply (intro compose_eq)
    using that by auto
  have F2[simp]: \<open>(\<phi>\<^sub>2 \<circ>\<^bsub>\<P>\<^esub> \<phi>\<^sub>1) x = \<phi>\<^sub>2 (\<phi>\<^sub>1 x)\<close> if \<open>y \<longlongrightarrow> x\<close> for x y
    apply (intro compose_eq)
    using that by auto
  show ?thesis
    apply (rule particular_struct_eqI ; auto)
    subgoal G1 for w
      by (intro exI[of _ \<open>\<phi>\<^sub>1 ` w\<close>] conjI  exI[of _ w] ; simp)
    subgoal G2 for w
      by (intro exI[of _ w] conjI ; simp?)
    subgoal G3
      (* \<open>lift_morph_2 \<Gamma> \<phi> p x y \<equiv> \<exists>x\<^sub>1 y\<^sub>1. p \<Gamma> x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1\<close> *)
      apply (intro ext iffI ; (elim exE conjE)? ; hypsubst_thin)
      subgoal for _ _ x y
        apply (rule exI[of _ \<open>\<phi>\<^sub>1 x\<close>] ; rule exI[of _ \<open>\<phi>\<^sub>1 y\<close>] ; intro conjI iffI ; simp?)
        by blast
      subgoal for _ _ _ _ x y
        by (rule exI[of _ x] ; rule exI[of _ y] ; auto)
      done
    subgoal G4
      apply (intro ext iffI ; (elim exE conjE)? ; hypsubst_thin)
      subgoal for _ q x
        by (rule exI[of _ \<open>\<phi>\<^sub>1 x\<close>] ; (intro conjI)? ; (rule exI[of _ x])? ; 
            (intro conjI)? ; simp?)
      subgoal for _ q _ x
        by (intro exI[of _ x] ; simp)
      done
    subgoal G5
      apply (intro ext iffI ; (elim exE conjE)? ; hypsubst_thin)
      subgoal for _ _ x y 
        apply (rule exI[of _ \<open>\<phi>\<^sub>1 x\<close>] ; rule exI[of _ \<open>\<phi>\<^sub>1 y\<close>] ; intro conjI ; simp?)
        by (rule exI[of _ x] ; rule exI[of _ y] ; intro conjI ; simp)
      subgoal for _ _ _ _ x y
        by (rule exI[of _ x] ; rule exI[of _ y] ; intro conjI ; simp)
      done
    done
qed

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> inj_morph_img_valid_structure:
  fixes \<phi> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close>
  assumes \<open>inj_on \<phi> \<P>\<close> \<open>\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f\<close> \<open>undefined \<notin> \<phi> ` \<P>\<close>
  shows \<open>particular_struct (MorphImg \<phi> \<Gamma>)\<close>
proof -
  define phi_inv (\<open>\<phi>\<inverse>\<close>) where \<open>\<phi>\<inverse> \<equiv> Inv \<P> \<phi>\<close>

  obtain phi_inv:
      \<open>\<And>x. x \<in> \<P> \<Longrightarrow> \<phi>\<inverse> (\<phi> x) = x\<close>
      \<open>\<And>x. x \<in> \<phi> ` \<P> \<Longrightarrow> \<phi> (\<phi>\<inverse> x) = x\<close>
      \<open>\<And>X. X \<subseteq> \<P> \<Longrightarrow> \<phi>\<inverse> ` \<phi> ` X = X\<close>
      \<open>\<And>X. X \<subseteq> \<phi> ` \<P> \<Longrightarrow> \<phi> ` \<phi>\<inverse> ` X = X\<close>
      \<open>\<And>X. \<phi>\<inverse> ` \<phi> ` (X \<inter> \<P>) = X \<inter> \<P>\<close>
      \<open>\<And>X. \<phi> ` \<phi>\<inverse> ` (X \<inter> \<phi> ` \<P>) = X \<inter> \<phi> ` \<P>\<close>
    using assms(1) that
    apply (simp add:  image_Inv_cancel phi_inv_def)    
    by (metis Inv_inj_surj image_Inv_cancel subset_imageE)

  have same_worlds: \<open>w\<^sub>1 = w\<^sub>2\<close> if as: \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>2 \<in> \<W>\<close> \<open>\<phi> ` w\<^sub>1 = \<phi> ` w\<^sub>2\<close> for w\<^sub>1 w\<^sub>2
    using as worlds_are_made_of_particulars assms(1)     
    by (metis phi_inv(3))

  have phi_img_inj: \<open>X = Y\<close> if \<open>X \<subseteq> \<P>\<close> \<open>Y \<subseteq> \<P>\<close> \<open>\<phi> ` X = \<phi> ` Y\<close> for X Y
    using that assms(1) by (meson inj_on_image_eq_iff)

  let \<open>?\<Gamma>'\<close> = \<open>MorphImg \<phi> \<Gamma>\<close>

  have morphI_eq[simp]: \<open>possible_worlds_sig.\<P> {\<phi> ` w |w. w \<in> \<W>} = \<phi> ` \<P>\<close>
    by (auto simp: possible_worlds_sig.\<P>_def)

  have A1: \<open>\<exists>w\<in>{\<phi> ` w |w. w \<in> \<W>}. x \<notin> w\<close> 
    if as: \<open>x \<in> possible_worlds_sig.\<P> {\<phi> ` w |w. w \<in> \<W>}\<close> for x
  proof -
    obtain w where AA: \<open>w \<in> \<W>\<close> \<open>x \<in> \<phi> ` w\<close>      
      apply (rule as[THEN possible_worlds_sig.\<P>_E] ; simp
            ; elim exE conjE ; hypsubst
            ; elim imageE ; hypsubst_thin)
      subgoal premises P for w\<^sub>1 w\<^sub>2 y                
        by (rule P(1)[of \<open>w\<^sub>2\<close>] ; simp add: P)
      done
    obtain BB: \<open>w \<subseteq> \<P>\<close> \<open>x \<in> \<phi> ` \<P>\<close> using AA
      worlds_are_made_of_particulars by blast      
    obtain y where CC: \<open>x = \<phi> y\<close> \<open>y \<in> w\<close> \<open>y \<in> \<P>\<close> 
      using AA(2) BB by blast
    obtain w' where DD: \<open>w' \<in> \<W>\<close> \<open>y \<notin> w'\<close> 
      using CC(3) particulars_do_not_exist_in_some_world by blast
    have EE: \<open>x \<notin> \<phi> ` w'\<close>         
        by (metis CC(1) CC(3) DD(1) DD(2) image_eqI phi_inv(1) phi_inv(3) worlds_are_made_of_particulars)
    show \<open>?thesis\<close>
      apply (intro bexI[of _ \<open>\<phi> ` w'\<close>] EE)
      using DD by auto
  qed

  let \<open>?\<W>\<close> = \<open>{\<phi> ` w |w. w \<in> \<W>}\<close>
  let \<open>?inheresIn\<close> = \<open>\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. x\<^sub>1 \<triangleleft> y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1\<close>
  let \<open>?assocQuale\<close> = \<open>\<lambda>x q. \<exists>x\<^sub>1. x\<^sub>1 \<leadsto> q \<and> x = \<phi> x\<^sub>1\<close>
  let \<open>?towards\<close> = \<open>\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. x\<^sub>1 \<longlongrightarrow> y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1\<close>
  
  interpret M: possible_worlds \<open>?\<W>\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales)
    subgoal has_inj using assms by blast
    subgoal using at_least_one_possible_world by auto
    subgoal using A1 by blast
    subgoal  
      apply (elim CollectE exE conjE ; hypsubst_thin)
      subgoal for w
        using assms(3) by blast
      done  
    done

  have Med_simp[simp]: \<open>M.ed x y \<longleftrightarrow> (\<exists>x\<^sub>1 y\<^sub>1. ed x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close> for x y
    apply (simp only: possible_worlds_sig.ed_def ; simp)
    apply (safe ; hypsubst_thin?)
    subgoal G1 premises P for x\<^sub>1 x\<^sub>2
      apply (rule exI[of _ \<open>x\<^sub>1\<close>] ; intro conjI P
            ; rule exI[of _ \<open>x\<^sub>2\<close>] ; intro conjI P ; simp?
            ; intro ballI impI)
      subgoal premises Q for w
        supply R1 = P(2)[rule_format,of \<open>\<phi> ` w\<close>,
            simplified image_def Bex_def,simplified,
            OF exI[of _ \<open>w\<close>],
            simplified,
            OF _ exI[of _ \<open>x\<^sub>2\<close>],
            simplified,OF _ conjI]         
        by (meson P Q assms(1) image_eqI inj_on_image_mem_iff worlds_are_made_of_particulars)
      done
    subgoal G2 premises P for x\<^sub>1 x\<^sub>2
      using P by blast
    subgoal G3 premises P for x\<^sub>1 x\<^sub>2
      using P by blast
    subgoal premises P for x\<^sub>1 x\<^sub>2 w\<^sub>1 w\<^sub>2 x\<^sub>3
      using P apply (simp add: image_def)
      apply (rule bexI[of _ \<open>x\<^sub>2\<close>] ; simp?)      
      by (metis \<P>_I phi_inv(1))
    done
          
      

  interpret M: inherence_base \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales ; simp?)
    subgoal G1 by auto
    subgoal G2 by (metis inherence_imp_ed)
    subgoal G3 by (metis bearer_eqI inherence_scope phi_inv(1))
    done

  interpret M: noetherian_inherence \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>TYPE('p\<^sub>1)\<close>
  proof (unfold_locales ; simp?)
    have AA: \<open>(\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. x\<^sub>1 \<triangleleft> y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<inverse>\<inverse> =
          (\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. (\<triangleleft>)\<inverse>\<inverse> x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close>
      by (intro ext ; simp ; blast)
    show \<open>wfP (\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. x\<^sub>1 \<triangleleft> y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<inverse>\<inverse>\<close>
      apply (subst AA)
      apply (intro wfI[to_pred,of _ \<open>\<phi> ` \<P>\<close> \<open>\<phi> ` \<P>\<close>] subsetI ; safe)
      subgoal using inherence_scope by auto
      subgoal using inherence_scope by auto
      subgoal premises P for x\<^sub>1 P x\<^sub>2 x\<^sub>3 
        using P
        apply (induct arbitrary: \<open>x\<^sub>2\<close> rule: inherence_is_noetherian[THEN wfP_induct])
        apply simp
        subgoal premises Q for x\<^sub>4 x\<^sub>5          
          apply (rule Q(2)[rule_format] ; elim exE conjE ; simp)
          subgoal premises T for x\<^sub>6 x\<^sub>7 x\<^sub>8
            apply (rule Q(1)[rule_format,of \<open>x\<^sub>7\<close> \<open>x\<^sub>7\<close>,simplified])    
            supply R1 = inj_onD[OF assms(1),OF T(3) Q(5),
                              OF inherence_scope[OF T(1),THEN conjunct1]]
            subgoal using T(1) R1 by simp
            using T(1) inherence_scope by simp
          done
        done
      done
  qed      

  interpret M: inherence \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales ; intro wfI[to_pred,of _ \<open>\<phi> ` \<P>\<close> \<open>\<phi> ` \<P>\<close>] ; safe)
    subgoal G1 by blast
    subgoal G2 by blast
    subgoal G3 premises P for x\<^sub>1 P x\<^sub>2 x\<^sub>3 
      using P
      apply (induct arbitrary: \<open>x\<^sub>2\<close> rule: inherence_is_wf[THEN wfP_induct])
      apply simp
      subgoal G3_1 premises Q for x\<^sub>4 x\<^sub>5          
        apply (rule Q(2)[rule_format] ; elim exE conjE ; simp)
        subgoal G3_1_1 premises T for x\<^sub>6 x\<^sub>7 x\<^sub>8
          apply (rule Q(1)[rule_format,of \<open>x\<^sub>7\<close> \<open>x\<^sub>7\<close>,simplified])   
          supply R1 = inj_onD[OF assms(1),OF T(3) Q(5),
                OF inherence_scope[OF T(1),THEN conjunct2]]
          subgoal G3_1_1_1 using T(1) R1 by simp
          using T(1) inherence_scope by simp
        done
      done
    done  

  have M_qual_particular[simp]: 
    \<open>qualified_particulars_sig.qualifiedParticulars (\<lambda>x q. \<exists>x\<^sub>1 w\<^sub>1. x\<^sub>1 \<leadsto> q \<and> x = \<phi> x\<^sub>1) =
      \<phi> ` \<P>\<^sub>q\<close>
    by (auto simp: qualified_particulars_sig.qualifiedParticulars_def)

  interpret M: qualified_particulars \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>\<Q>\<S>\<close>  \<open>?assocQuale\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales)
    subgoal G1 for x q
      using assoc_quale_scopeD inheres_in_bearerI by blast 
    subgoal G2 for x q\<^sub>1 q\<^sub>2
      apply (elim exE conjE ; hypsubst_thin)
      subgoal premises P for x\<^sub>1 x\<^sub>2 
        supply S1 = assoc_quale_scopeD[OF P(1)]
        supply S2 = assoc_quale_scopeD[OF P(2)]
        supply q1q2 = inj_onD[OF assms(1),OF P(3) S1(1) S2(1)] 
        using P(1,2)[simplified  q1q2] assoc_quale_unique 
        by blast
      done
    subgoal G3 for w y\<^sub>1 y\<^sub>2 x q\<^sub>1 q\<^sub>2 Q
      apply (elim imageE exE conjE ; simp ; elim exE conjE imageE ; hypsubst_thin
            ; elim imageE ; simp)
      by (metis \<P>_I assoc_quale_scopeD(1) inherence_scope phi_inv(1) quality_moment_unique_by_quality_space)
    subgoal G4 for Q            
      using every_quality_space_is_used by blast
    subgoal G5 using quale_determines_moment
      by (metis assoc_quale_scopeD(3) endurantI1 inherence_scope phi_inv(1))
    done

  have M_M_eq[simp]: \<open>M.\<M> = \<phi> ` \<M>\<close>
    by (auto simp: inherence_sig.\<M>_def)

  have trans_inheres_in_scopeD: \<open>x \<in> \<M>\<close> \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> if \<open>x \<triangleleft>\<triangleleft> y\<close> for x y    
    using that trans_inheres_in_scope by blast+

  have M_inheres_in_trancl[simp]:
    \<open>?inheresIn\<^sup>+\<^sup>+ x y \<longleftrightarrow> (\<exists>x\<^sub>1 y\<^sub>1. (\<triangleleft>)\<^sup>+\<^sup>+ x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close> for x y
    apply (intro iffI)
    subgoal G1
      apply (induct rule: tranclp.induct)
      subgoal G1_1 for x\<^sub>1 y\<^sub>1
        apply (elim exE conjE ; hypsubst_thin)
        subgoal G1_1_1 for x\<^sub>2 y\<^sub>2
          by (rule exI[of _ \<open>x\<^sub>2\<close>] ; rule exI[of _ \<open>y\<^sub>2\<close>] ; simp)
        done
      subgoal G1_2 for x\<^sub>1 y\<^sub>1 z\<^sub>1
        apply (elim exE conjE ; hypsubst_thin)
        subgoal G1_2_1 premises P for x\<^sub>2 x\<^sub>3 y\<^sub>2 y\<^sub>3
          supply S1 = inherence_scope[OF P(3),THEN conjunct1]
                     inherence_scope[OF P(3),THEN conjunct2]
          supply S2 = trans_inheres_in_scopeD[OF P(2)]
          supply y2x3 = inj_onD[OF assms(1),OF P(4) _ S1(1),OF S2(3)]
          supply P1 = P(1,2,3)[simplified y2x3]
          supply R1 = tranclp.intros(2)[of \<open>(\<triangleleft>)\<close>,OF P(2),simplified y2x3,OF P(3)]           
          apply (rule exI[of _ \<open>x\<^sub>2\<close>] ; rule exI[of _ \<open>y\<^sub>3\<close>])
          using R1 by simp
        done
      done    
    subgoal G2
      apply (elim exE conjE ; hypsubst_thin)
      subgoal G2_1 for x\<^sub>1 y\<^sub>1
        apply (induct rule: tranclp.induct)
        subgoal G2_1_1 by auto
        subgoal G2_1_2 for x\<^sub>2 y\<^sub>2 z\<^sub>2
          apply (rule tranclp.intros(2)[of \<open>?inheresIn\<close>, of \<open>\<phi> x\<^sub>2\<close> \<open>\<phi> y\<^sub>2\<close> \<open>\<phi> z\<^sub>2\<close>] ; simp?)
          subgoal premises P
            by (rule exI[of _ \<open>y\<^sub>2\<close>] ; rule exI[of _ \<open>z\<^sub>2\<close>] ; simp add: P)
          done
        done
      done
    done

  have M_inheres_in_rtranclp[simp]:
    \<open>?inheresIn\<^sup>*\<^sup>* x y \<longleftrightarrow> x = y \<or> (\<exists>x\<^sub>1 y\<^sub>1. (\<triangleleft>)\<^sup>+\<^sup>+ x\<^sub>1 y\<^sub>1 \<and> x = \<phi> x\<^sub>1 \<and> y = \<phi> y\<^sub>1)\<close> for x y    
    by (simp add: Nitpick.rtranclp_unfold)

  have ed_scope: \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close> if \<open>ed x y\<close> for x y
    using that edE by blast+
      

  have M_ultimateBearer[simp]: 
    \<open>M.ultimateBearer (\<phi> x) = \<phi> (ultimateBearer x)\<close> if as: \<open>x \<in> \<P>\<close> for x
    using as 
    apply (subst Inherence.noetherian_inherence.ultimate_bearer_eq_simp[
        of \<open>?\<W>\<close> \<open>?inheresIn\<close>,
          simplified,OF M.noetherian_inherence_axioms])
    apply auto
    subgoal G1 by (meson \<S>_E image_eqI ultimate_bearer_substantial)
    subgoal G2 by (metis endurantI1 inherence_sig.\<S>_E phi_inv(1) ultimate_bearer_substantial)      
    by (metis relpowp_imp_rtranclp rtranclpD ultimate_bearer_and_order)

  have M_directed_moments[simp]: \<open>towardness_sig.directed_moments ?towards = \<phi> ` \<M>\<^sub>\<rightarrow>\<close>
    by (auto simp: towardness_sig.directed_moments_def image_def Bex_def)

  interpret M: towardness \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>?towards\<close> \<open>TYPE('p\<^sub>1)\<close>
    apply (unfold_locales ; simp?)
    subgoal G1 for x y
      apply (elim exE conjE ; hypsubst_thin)      
      apply (intro conjI ; simp add: image_def inherence_sig.\<S>_def possible_worlds_sig.\<P>_def)
      subgoal G1_1 by blast
      subgoal G1_2 for x\<^sub>1 y\<^sub>1
        apply (intro conjI ballI)
        subgoal G1_2_1 by (metis \<P>_E image_def image_eqI towardness_scopeD(3))
        by (metis \<S>_E assms(1) endurantI1 inj_on_contraD towardness_scope)
      done
    subgoal G2 for x y  
      apply (elim exE conjE ; hypsubst_thin)
      subgoal for x\<^sub>1 y\<^sub>1
        apply (rule exI[of _ \<open>x\<^sub>1\<close>] ; rule exI[of _ \<open>y\<^sub>1\<close>] ; simp)        
        by (simp add: towardness_imp_ed)
      done      
    subgoal G3 using towardness_diff_ultimate_bearers 
      by (smt M_ultimateBearer endurantI1 inherence_sig.\<S>_E noetherian_inherence.ultimate_bearer_substantial noetherian_inherence_axioms phi_inv(1) towardness_scope)
    subgoal G4 using towardness_single by (metis endurantI1 phi_inv(1) towardness_apply_to_moments)
    done

  interpret M: ufo_particular_theory_sig \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>\<Q>\<S>\<close> \<open>?assocQuale\<close> \<open>?towards\<close> \<open>TYPE('p\<^sub>1)\<close> .

  interpret M: ufo_particular_theory \<open>?\<W>\<close> \<open>?inheresIn\<close> \<open>\<Q>\<S>\<close> \<open>?assocQuale\<close> \<open>?towards\<close> \<open>TYPE('p\<^sub>1)\<close>
  proof (unfold_locales ; simp ; intro allI impI ; hypsubst_thin
          ; elim M.qualifiedParticularsE exE conjE ; hypsubst_thin)
    fix x\<^sub>1 y\<^sub>1 q x\<^sub>2
    assume as: \<open>x\<^sub>1 \<triangleleft> y\<^sub>1\<close> \<open>x\<^sub>2 \<leadsto> q\<close>  
    show \<open>\<phi> x\<^sub>2 \<noteq> \<phi> y\<^sub>1\<close>
    proof 
      obtain A: \<open>x\<^sub>1 \<in> \<P>\<close> \<open>y\<^sub>1 \<in> \<P>\<close> \<open>x\<^sub>2 \<in> \<P>\<close> 
        using as(1,2) inherence_scope        
        by (simp add: assoc_quale_scopeD(1))
      assume \<open>\<phi> x\<^sub>2 =  \<phi> y\<^sub>1\<close>
      then have \<open>x\<^sub>2 = y\<^sub>1\<close> using \<open>inj_on \<phi> \<P>\<close>[THEN inj_onD] A by blast
      then have \<open>y\<^sub>1 \<leadsto> q\<close> using as(2) by simp
      then show False using as(1) 
        using qualified_particulars_are_not_bearers by blast      
    qed
  qed
     
  show \<open>?thesis\<close>
    apply (simp add: particular_struct_def)
    using M.ufo_particular_theory_axioms by simp
qed
   

lemma \<^marker>\<open>tag (proof) aponly\<close> inj_morph_img_isomorphism[intro]:
  fixes \<phi> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close>
  assumes \<open>inj_on \<phi> \<P>\<close> \<open>\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f\<close> 
          \<open>\<phi> \<in> extensional \<P>\<close> \<open>undefined \<notin> \<phi> ` \<P>\<close>
  shows \<open>particular_struct_bijection_1 \<Gamma> \<phi>\<close>
proof -
  have A:\<open> x \<notin> \<E> \<Longrightarrow> \<phi> x = undefined\<close> for x
    using assms(3)
    by (simp add: extensional_def ; metis)
  interpret M: particular_struct \<open>MorphImg \<phi> \<Gamma>\<close> \<open>TYPE('p\<^sub>1)\<close>
    using inj_morph_img_valid_structure[OF assms(1,2,4)] .
  have B: \<open>\<phi> x = undefined\<close> if \<open>\<forall>w\<in>\<W>. x \<notin> w\<close> for x
    apply (intro A)
    using that by auto
    
  interpret I: pre_particular_struct_morphism \<Gamma> \<open>MorphImg \<phi> \<Gamma>\<close> \<phi>
    apply (simp add: pre_particular_struct_morphism_def
        M.ufo_particular_theory_axioms
        M.particular_struct_axioms
        ufo_particular_theory_axioms)
    apply (unfold_locales ; simp add: inherence_sig.\<S>_def possible_worlds_sig.\<P>_def inherence_sig.\<M>_def extensional_def; auto? )
    subgoal G1 by (metis \<P>_I assms(1) inherence_scope inj_on_eq_iff)
    subgoal G2 using B by metis
    subgoal G3 by (metis \<P>_I assms(1) inherence_scope inj_onD)
    subgoal G4 by (metis \<P>_I assms(1) inj_onD towardness_scopeD(2) towardness_scopeD(3)) 
    subgoal G5 by (metis Union_iff possible_worlds_sig.\<P>_def towardness_scopeD(3))
    subgoal G6 by (metis \<P>_I assms(1) assoc_quale_scopeD(1) inj_on_eq_iff)
    done
    
  interpret I: particular_struct_morphism \<Gamma> \<open>MorphImg \<phi> \<Gamma>\<close> \<phi>
    apply (unfold_locales ; simp add: I.world_corresp_def
        ; (elim exE conjE)? ; hypsubst_thin?
        ; (elim imageE)? ; hypsubst_thin?)
    by (metis assms(1) inj_on_image_mem_iff worlds_are_made_of_particulars)+    

  interpret I: particular_struct_injection \<Gamma> \<open>MorphImg \<phi> \<Gamma>\<close> \<phi>    
    apply (unfold_locales)    
    by (simp add: assms(1))

  interpret I: particular_struct_surjection \<Gamma> \<open>MorphImg \<phi> \<Gamma>\<close> \<phi>
    by (unfold_locales ; auto simp: possible_worlds_sig.\<P>_def)    
  
  show \<open>?thesis\<close>
    by (unfold_locales)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> inj_morph_img_BijMorphs:
  fixes \<phi> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close>
  assumes \<open>inj_on \<phi> \<P>\<close> \<open>\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f\<close> \<open>\<phi> \<in> extensional \<P>\<close> 
          \<open>undefined \<notin> \<phi> ` \<P>\<close>
  shows \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close>
  apply (intro bijections_I)
  using assms inj_morph_img_isomorphism by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> BijMorphs_iff_inj[simp]:  
  \<open>(\<phi> :: 'p \<Rightarrow> 'p\<^sub>1) \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub> \<longleftrightarrow> 
    inj_on \<phi> \<P> \<and> (\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f) \<and> \<phi> \<in> extensional \<P>
        \<and> undefined \<notin> \<phi> ` \<P>\<close>
proof (intro iffI ; (elim conjE)?)  
  show \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close> 
    if as: \<open>inj_on \<phi> \<E>\<close> \<open>\<exists>f::'p\<^sub>1 \<Rightarrow> ZF. inj f\<close> \<open>\<phi> \<in> extensional \<P>\<close> 
           \<open>undefined \<notin> \<phi> ` \<P>\<close>
    by (intro inj_morph_img_BijMorphs[OF as])
  show \<open>inj_on \<phi> \<P> \<and>  (\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f) \<and> \<phi> \<in> extensional \<P>
          \<and> undefined \<notin> \<phi> ` \<P>\<close> 
    if as: \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close> for \<phi> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close> and X
  proof (intro conjI)
    interpret I1: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
      using as by blast
    show \<open>inj_on \<phi> \<E>\<close> using I1.morph_is_injective by simp
    show \<open>\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f\<close> using I1.tgt.injection_to_ZF_exist .
    show \<open>\<phi> \<in> extensional \<P>\<close> using I1.morphism_extensional by simp
    show \<open>undefined \<notin> \<phi> ` \<P>\<close> using I1.undefined_not_in_img by simp    
  qed
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphism_1_iff_inj[simp]:  
  \<open>particular_struct_bijection_1 \<Gamma> (\<phi> :: 'p \<Rightarrow> 'p\<^sub>1) \<longleftrightarrow>
       inj_on \<phi> \<P> \<and> (\<exists>(f :: 'p\<^sub>1 \<Rightarrow> ZF). inj f) \<and> \<phi> \<in> extensional \<P>
       \<and> undefined \<notin> \<phi> ` \<P>\<close>
  using BijMorphs_iff_inj
  apply (simp only: bijections1_def)  
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> Perms_iff_inj[simp]:  
\<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub> \<longleftrightarrow> inj_on \<phi> \<P> \<and> MorphImg \<phi> \<Gamma> = \<Gamma> \<and> \<phi> \<in> extensional \<P>
                  \<and> undefined \<notin> \<phi> ` \<P>\<close>
proof -
  have A: \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE('p)\<^esub>\<close> 
    if as: \<open>inj_on \<phi> \<P>\<close> \<open>\<phi> \<in> extensional \<P>\<close> \<open>undefined \<notin> \<phi> ` \<P>\<close>
    using inj_morph_img_BijMorphs[OF as(1) _ as(2)] injection_to_ZF_exist    
    by (simp add: as)
  have B: \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close> 
    if as: \<open>inj_on \<phi> \<P>\<close> and as1[simp]: \<open>MorphImg \<phi> \<Gamma> = \<Gamma>\<close> 
       and extens: \<open>\<phi> \<in> extensional \<P>\<close> 
       and undef: \<open>undefined \<notin> \<phi> ` \<P>\<close>
  proof -
    interpret I: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close> 
      using A as extens undef by blast
    interpret I1: particular_struct_permutation \<open>\<Gamma>\<close> \<open>\<phi>\<close> 
      apply (simp add: particular_struct_permutation_def
              I.particular_struct_bijection_axioms[simplified as1])
      apply intro_locales
      using I.particular_struct_morphism_axioms[simplified as1]
        I.pre_particular_struct_morphism_axioms[simplified as1]
      by (simp add: particular_struct_morphism_def
                    pre_particular_struct_morphism_def)+
    show \<open>?thesis\<close>  
      using I1.particular_struct_permutation_axioms by blast
  qed
  have C: \<open>inj_on \<phi>' \<P> \<and> MorphImg \<phi>' \<Gamma> = \<Gamma> \<and> \<phi>' \<in> extensional \<P>
            \<and> undefined \<notin> \<phi>' ` \<P>\<close> if \<open>\<phi>' \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close> for \<phi>'
  proof -
    interpret I1: particular_struct_permutation \<open>\<Gamma>\<close> \<open>\<phi>'\<close> 
      using that by blast    
    interpret I: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>'\<close>
      using I1.particular_struct_permutation_to_isomorphism_1 by simp
    show \<open>inj_on \<phi>' \<P> \<and> MorphImg \<phi>' \<Gamma> = \<Gamma> \<and> \<phi>' \<in> extensional \<P>
          \<and> undefined \<notin> \<phi>' ` \<P>\<close>
      using I.morph_is_injective I.morphism_extensional
        I.undefined_not_in_img by auto
  qed
  show \<open>?thesis\<close>
    apply (intro iffI ; (elim conjE)?)
    subgoal by (rule C ; simp)
    subgoal by (rule B ; simp)
    done
qed
      
end

context particular_struct_bijection_1
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> phi_in_iso_morphs[intro]: 
  \<open>\<phi> \<in> BijMorphs1\<^bsub>src.\<Gamma>,X\<^esub>\<close>
  apply simp
  using tgt.injection_to_ZF_exist  
  using morph_is_surjective undefined_not_in_img by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_in_src_iso_models[intro]:  
  \<open>MorphImg \<phi> src.\<Gamma> \<in> IsoModels\<^bsub>src.\<Gamma>,X\<^esub>\<close>
  by (intro isomorphic_models_I[of \<open>\<phi>\<close>] phi_in_iso_morphs ; simp )

lemma \<^marker>\<open>tag (proof) aponly\<close> tgt_Gamma_eq_Morph_img[simp]: \<open>tgt.\<Gamma> = MorphImg \<phi> src.\<Gamma>\<close>
  apply (simp add: MorphImg_def)
  by (intro particular_struct_eqI ext ; simp add: ufo_particular_theory_sig.\<Gamma>_def)

interpretation \<^marker>\<open>tag (proof) aponly\<close> 
  inv_morph: particular_struct_bijection_1 
    \<open>MorphImg \<phi> src.\<Gamma>\<close> 
    \<open>\<phi>\<inverse>\<close> 
    \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
  apply (intro tgt.inj_morph_img_isomorphism[
         simplified tgt_Gamma_eq_Morph_img] ; simp?)    
  subgoal G2 using src.injection_to_ZF_exist .  
  subgoal G3 by (metis Inv_extensional morph_is_surjective)  
  using phi_inv_img src.undefined_not_in_particulars by auto
  
  
lemma \<^marker>\<open>tag (proof) aponly\<close> preserves_morphisms_src_tgt:
  fixes \<sigma> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>3\<close>
  assumes \<open>particular_struct_morphism src.\<Gamma> \<Gamma>' \<sigma>\<close>
  shows \<open>particular_struct_morphism tgt.\<Gamma> \<Gamma>' (\<sigma> \<circ>\<^bsub>particulars tgt.\<Gamma>\<^esub> \<phi>\<inverse>)\<close>
  apply (intro particular_struct_morphism_comp[OF _ assms])
  by (metis inv_is_bijective_morphism inv_morph.particular_struct_morphism_axioms particular_struct_bijection_1.tgt_Gamma_eq_Morph_img particular_struct_bijection_iff_particular_struct_bijection_1 tgt_Gamma_eq_Morph_img)

end
 
lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphisms_respect_morphisms:
  fixes \<sigma>   :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>3\<close> and \<phi> :: \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close> 
    and \<Gamma>   :: \<open>('p\<^sub>1,'q) particular_struct\<close>
    and \<Gamma>\<^sub>\<sigma> :: \<open>('p\<^sub>3,'q) particular_struct\<close>
  assumes \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,X\<^esub>\<close> \<open>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,\<Gamma>\<^sub>\<sigma>\<^esub>\<close>          
  shows \<open>\<sigma> \<circ>\<^bsub>\<phi> ` particulars \<Gamma>\<^esub> (invMorph \<Gamma> \<phi>) \<in> Morphs\<^bsub>MorphImg \<phi> \<Gamma>,\<Gamma>\<^sub>\<sigma>\<^esub>\<close>
proof -
  interpret I1: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
    using assms(1) by blast
  interpret I2: particular_struct_morphism \<open>\<Gamma>\<close> \<open>\<Gamma>\<^sub>\<sigma>\<close> \<open>\<sigma>\<close>
    using assms by auto
  have S1: \<open>I1.tgt.\<Gamma> = MorphImg \<phi> \<Gamma>\<close> using I1.tgt.\<Gamma>_simps by blast 
  interpret I3: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<open>I1.inv_morph\<close>
    apply (simp only: I1.tgt.isomorphism_1_iff_inj[simplified S1]
          ; intro conjI ; simp?)
    subgoal   using I1.src.injection_to_ZF_exist by simp    
    subgoal by (metis I1.morph_is_surjective Inv_extensional)    
    using I1.phi_inv_img I1.src.undefined_not_in_particulars by auto
  have A: \<open>I1.src.\<Gamma> = \<Gamma>\<close> by auto
  have B: \<open>I3.src.\<Gamma> = MorphImg \<phi> \<Gamma>\<close> 
    by (intro particular_struct_eqI ; simp only: I3.src.\<Gamma>_simps)  
  have C: \<open>I3.tgt.endurants = I1.src.endurants\<close>
    apply (auto simp: possible_worlds_sig.\<P>_def)
    subgoal for x w
      apply (intro bexI[of _ \<open>w\<close>] ; simp?)            
      using I1.src.\<P>_def particular_struct_bijection.tgt_is_morph_img by force
    subgoal for x w
      apply (intro bexI[of _ \<open>w\<close>] ; simp?)            
      using I1.src.\<P>_def particular_struct_bijection.tgt_is_morph_img by force
    done
  have D: \<open>MorphImg I1.inv_morph (MorphImg \<phi> \<Gamma>) = \<Gamma>\<close>    
    apply (intro particular_struct_eqI ; simp?)    
    subgoal using particular_struct_bijection_iff_particular_struct_bijection_1 by force
    subgoal by (metis I1.inv_is_bijective_morphism particular_struct_bijection_iff_particular_struct_bijection_1)
    subgoal using particular_struct_bijection.tgt_is_morph_img by fastforce
    subgoal by (metis I1.inv_is_bijective_morphism I3.particular_struct_bijection_axioms isomorphism_tgt_unique)
    done
  show \<open>?thesis\<close>
    apply (intro morphs_I particular_struct_morphism_comp[of _ \<open>\<Gamma>\<close>]
            I2.particular_struct_morphism_axioms)
    using D I2.particular_struct_morphism_axioms 
      I3.particular_struct_morphism_axioms particular_struct_morphism_comp 
    by fastforce    
qed

context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphs_to_zf_non_empty[simp]: \<open>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> \<noteq> \<emptyset>\<close>
proof -  
  obtain \<sigma> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>inj \<sigma>\<close>  using injection_to_ZF_exist by blast
  define \<theta> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>\<theta> x = Opair undefined (\<sigma> x)\<close> for x
  define f where \<open>f = restrict \<theta> \<E>\<close>
  have A[simp]: \<open>undefined \<noteq> Opair undefined x\<close> for x    
    by (metis Elem_Opair_exists notsym_Elem)
  have B[simp]: \<open>undefined \<notin> f ` \<E>\<close>
    by (auto simp add: f_def \<theta>_def)
  have C[simp]: \<open>f \<in> extensional \<E>\<close>
    by (simp add: extensional_def f_def)
  have D[simp]: \<open>inj_on \<sigma> \<E>\<close>
    using inj_on_subset[OF \<open>inj \<sigma>\<close>] by auto
  have E[simp]: \<open>inj_on \<theta> \<E>\<close>
    apply (intro inj_onI ; simp add: \<theta>_def)
    subgoal for x y
      apply (rule D[THEN inj_onD,of x y] ; simp?)      
      by (meson Opair)
    done
  have F[simp]: \<open>inj_on f \<E>\<close>
    using E by (simp add: f_def)
  have \<open>particular_struct_bijection_1 \<Gamma> f\<close>    
    apply (intro inj_morph_img_isomorphism  ; simp?)
    using \<open>inj \<sigma>\<close> by blast    

  then have \<open>f \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> by simp
  then show ?thesis by blast    
qed

end

end
