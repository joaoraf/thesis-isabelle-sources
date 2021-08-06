text_raw \<open>\section[Isomorphism-invariant Instantiation]{Isomorphism-invariant Instantiation\isalabel{sec:instantiation}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  From \autoref{cha:simplified-ufo-theory} to \autoref{cha:individuality}, we
  mainly discussed concepts related to UFO \emph{particulrs}, with a brief
  mention, on \autoref{sec:universals}, of a minimal theory of universals
  and instantiation. However, since this chapter focuses on the concept of
  \emph{sortality}, which is applicable to UFO \emph{substantial universals},
  it's necessary to present a more detailed theory of instantiation.

  In particular, it is necessary to adapt the usual notion of instantiation
  to the structural framework introduced in \autoref{cha:particular-structures}.
  This section describes a characterization of identity that follows a strategy
  similar to the one used in characterizing isomorphically invariant identification
  predicate described in \autoref{sec:identifiability}. We use a shift in the
  type of particulars to hide the details of a particular representations and
  guarantee that the instantiation relation only relies on the formal elements
  that are provided in the UFO particular structure. In other words, the instantiation
  relation is isomorphically invariant.
  
  The identity relation, in UFO, is a contigent relation between particulars and
  universals. Whether it holds or not depends also on which possible world we are
  considering it. On the other hand, the instantiation relation may also depend
  on other particulars and their properties, e.g. the universal \emph{Being Next to
  a Black Cat}. Thus, we condider an instantiation predicate one that satisfies the
  following type:
\<close>
text_raw \<open>\par\<close>
theory Instantiation
  imports 
    "../ParticularStructures/MorphismImage" 
    "../Universals/Universals"

begin

type_synonym ('q,'u) iof_predicate =
  \<open>(ZF,'q) particular_struct \<Rightarrow> ZF \<Rightarrow> ZF set \<Rightarrow> 'u \<Rightarrow> bool\<close>


locale iso_invariant_iof_predicate_sig =
  fixes zf_iof :: \<open>('q,'u) iof_predicate\<close> and
        Typ\<^sub>q :: \<open>'q itself\<close> and
        Typ\<^sub>u :: \<open>'u itself\<close>

locale iso_invariant_iof_predicate =
    iso_invariant_iof_predicate_sig  + 
  assumes
    zf_iof_scope:
        \<open>zf_iof \<Gamma> x w U \<Longrightarrow> w \<in> ps_worlds \<Gamma> \<and> x \<in> w\<close> and
    invariant_under_isomorphisms:
      \<open>\<lbrakk> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>  
       ; x \<in> particulars \<Gamma>
       ; w \<in> ps_worlds \<Gamma>       
        \<rbrakk> \<Longrightarrow>
        zf_iof \<Gamma> x  w U \<longleftrightarrow> zf_iof (MorphImg \<phi> \<Gamma>) (\<phi> x) (\<phi> ` w) U\<close>
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
   However, we also want the instantiation relation to fit into our structural 
   approach. To do so, we require it to satisfy the following axioms, where
   @{term_type \<open>zf_iof\<close>} is the instantiation relation and 
   the term \<open>zf_iof \<Gamma> x w U\<close> denotes that ``\<open>x\<close>, a particular of \<open>\<Gamma>\<close>, instantiates \<open>U\<close> in
   the possible world \<open>w\<close> of \<open>\<Gamma>\<close>'':


\begin{axiom}{$@{thm_name zf_iof_scope}$}
If \<open>zf_iof \<Gamma> x w U\<close> holds, then \<open>w\<close> is a possible world of \<open>\<Gamma>\<close>
and \<open>x\<close> exists in \<open>w\<close>:

\[ @{thm zf_iof_scope} \]
\end{axiom}

\begin{axiom}{$@{thm_name invariant_under_isomorphisms}$}
\<open>zf_iof\<close> must be invariant under \<open>\<Gamma>\<close>-bijections:

\begin{align*}
 & \llbracket @{thm (prem 1) invariant_under_isomorphisms} ; \\
 & @{thm (prem 2) invariant_under_isomorphisms} ; \\
 & @{thm (prem 3) invariant_under_isomorphisms} \rrbracket \Longrightarrow \\
 & @{thm (concl) invariant_under_isomorphisms}
\end{align*}

\end{axiom}
\<close>
text_raw \<open>\par\<close>
lemma  \<^marker>\<open>tag (proof) aponly\<close> invariant_under_isomorphisms_A:
  assumes 
    \<open>particular_struct_bijection_1 \<Gamma> \<phi>\<close>
    \<open>x \<in> particulars \<Gamma>\<close>
    \<open>w \<in> ps_worlds \<Gamma>\<close>
  shows \<open>zf_iof \<Gamma> x  w U \<longleftrightarrow> zf_iof (MorphImg \<phi> \<Gamma>) (\<phi> x) (\<phi> ` w) U\<close>
  using invariant_under_isomorphisms[OF _ assms(2,3)]
    assms(1) by blast

end

context particular_struct_bijection_1
begin

declare src.isomorphism_1_iff_inj[simp del]

lemma  \<^marker>\<open>tag (proof) aponly\<close> invariant_under_isomorphisms_B:
  fixes zf_iof :: \<open>('q,'u) iof_predicate\<close>
  assumes 
    \<open>iso_invariant_iof_predicate zf_iof\<close>
    \<open>inj_on (f :: 'p\<^sub>1 \<Rightarrow> ZF) (particulars \<Gamma>\<^sub>1)\<close>
    \<open>inj_on (g :: 'p\<^sub>2 \<Rightarrow> ZF) (\<phi> ` particulars \<Gamma>\<^sub>1)\<close>
    \<open>x \<in> src.\<P>\<close>
    \<open>w \<in> src.\<W>\<close>
    
  shows \<open>zf_iof (MorphImg f \<Gamma>\<^sub>1) (f x)  (f ` w) U \<longleftrightarrow> 
         zf_iof (MorphImg (g \<circ> \<phi>) \<Gamma>\<^sub>1) (g (\<phi> x)) (g ` \<phi> ` w) U\<close>
proof -
  have inj_ZF[intro!,simp]: \<open>\<exists>(f :: ZF \<Rightarrow> ZF). inj f\<close> using inj_on_id by blast
  have A[simp]: 
    \<open>ufo_particular_theory_sig.\<Gamma> \<W>\<^sub>\<phi> (\<triangleleft>\<^sub>\<phi>) src.\<Q>\<S> (\<leadsto>\<^sub>\<phi>) (\<longlongrightarrow>\<^sub>\<phi>) 
            = MorphImg \<phi> \<Gamma>\<^sub>1\<close>
    by (auto simp: ufo_particular_theory_sig.\<Gamma>_def
            particular_struct_morphism_image_simps)
  have A1[simp]: \<open>src.\<Gamma> = \<Gamma>\<^sub>1\<close> by auto
  interpret f: particular_struct_bijection_1 \<Gamma>\<^sub>1 f \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE(ZF)\<close>
    using src.inj_morph_img_isomorphism[OF inj_on_subset[OF assms(2)]
            , simplified] by simp
  interpret g: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> g \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE(ZF)\<close>
    using tgt.inj_morph_img_isomorphism[OF inj_on_subset[OF assms(3)]
            , simplified] .
  have B[simp]: \<open>MorphImg f.inv_morph (MorphImg f \<Gamma>\<^sub>1) = \<Gamma>\<^sub>1\<close>
    by (metis f.particular_struct_bijection_axioms 
          particular_struct_bijection.inv_is_bijective_morphism 
          particular_struct_bijection_iff_particular_struct_bijection_1)
  have C: \<open>f x \<in> f.tgt.\<P>\<close> using assms(4) by blast
  have D: \<open>f ` w \<in> f.\<W>\<^sub>\<phi>\<close> using assms(5) by blast
  interpret phi_zf: 
    particular_struct_bijection_1 
      \<open>MorphImg f \<Gamma>\<^sub>1\<close> 
      \<open>g \<circ> \<phi> \<circ> f.inv_morph\<close> 
      \<open>TYPE(ZF)\<close> \<open>TYPE(ZF)\<close>
    apply (intro particular_struct_bijection_1_comp ; (simp only: B)?)
    subgoal 
      using particular_struct_bijection_iff_particular_struct_bijection_1 
      by blast
    subgoal using particular_struct_bijection_1_axioms by simp    
    using g.particular_struct_bijection_1_axioms by blast

  interpret iso_invariant_iof_predicate zf_iof using assms(1) by simp
  have x_inv_f[simp]: \<open>f.inv_morph (f x) = x\<close> using assms(4) by auto
  have w_inv_f[simp]: \<open>f.inv_morph ` f ` w = w\<close> using assms(5) by auto
  show ?thesis
    by (simp only: invariant_under_isomorphisms_A[
      OF phi_zf.particular_struct_bijection_1_axioms, OF C D,of U
      ] o_apply image_comp[symmetric] x_inv_f w_inv_f
      ; simp)
qed


end

locale iso_instantiation_sig =
    ufo_particular_theory_sig where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q +
    iso_invariant_iof_predicate_sig where Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> and
    Typ\<^sub>u :: \<open>'u itself\<close>
begin


text \<^marker>\<open>tag bodyonly\<close> \<open>
  Up to this point, we defined an instantiation relation as a relation
  over particular structures whose type of particulars is the
  type of ZF sets. However, since we require the existence of
  an injection from whatever type of particulars a particular
  structure uses to the type of ZF sets, we can define the
  usual ternary instantiation relation in the context of an
  arbitrary particular structure as:
\<close>
text_raw \<open>\par\<close>
definition iof (\<open>_ \<Colon>\<^bsub>_\<^esub> _\<close> [74,1,74] 75) where
  \<open>x \<Colon>\<^bsub>w\<^esub> U \<longleftrightarrow> 
    (\<exists>f. inj_on f \<P> \<and> x \<in> \<P> 
       \<and> w \<in> \<W> 
       \<and> zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In other words, we apply \<open>zf_iof\<close> to the particular structure that
  is the image of some injection from \<open>\<P>\<close> to the type of ZF sets,
  which gives rise to an particular structure that is isomorphic to 
  \<open>\<Gamma>\<close>.
\<close>
text_raw \<open>\par\<close>
lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_I[intro]:
  assumes \<open>inj_on f \<P>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> \<P>\<close> \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close>
  shows \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  using assms by (auto simp: iof_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_E1:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  obtains f where 
    \<open>inj_on f \<P>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> \<P>\<close>  
    \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close>
  using assms by (auto simp: iof_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_scope_world:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>w \<in> \<W>\<close> 
  using assms by (auto simp: iof_def)

end

sublocale \<^marker>\<open>tag aponly\<close> iso_instantiation_sig \<subseteq> instantiation_sig 
  where iof = iof .


context iso_instantiation_sig
begin
notation \<^marker>\<open>tag aponly\<close> subsumes (infix \<open>\<sqsubseteq>\<close> 75)

end

locale iso_instantiation = 
    iso_instantiation_sig where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u +
    ufo_particular_theory where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q +
    iso_invariant_iof_predicate where Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> and
    Typ\<^sub>u :: \<open>'u itself\<close> 
begin

lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_E[elim]:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  obtains f where 
    \<open>inj_on f \<P>\<close> \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>U \<in> \<U>\<close> 
    \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close> \<open>x \<in> w\<close>
proof -
  obtain f where 
    A: \<open>inj_on f \<E>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> \<P>\<close> 
       \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close>
    using assms iof_E1 by blast
  have B: \<open>U \<in> \<U>\<close> using assms by blast
  interpret f: particular_struct_bijection_1 \<Gamma> f 
    apply simp
    using A(1) inj_on_id by blast  
  obtain \<open>f ` w \<in> f.\<W>\<^sub>\<phi>\<close> \<open>f x \<in> f ` w\<close> 
    using zf_iof_scope[OF A(4)] by metis
  then have \<open>x \<in> w\<close> using A(2,3)f.tgt_world_corresp_inv_image by force
  then show ?thesis using A B that  by metis
qed
      
lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_scope:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>U \<in> \<U>\<close> \<open>x \<in> w\<close>
  using assms zf_iof_scope by blast+
 
end

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The characterization of instantiation through an isomorphically invariant
  relation satisfies the axioms of an instantiation theory (\autoref{sec:universals}):
\<close>
text_raw \<open>\par\<close>
sublocale 
  iso_instantiation \<subseteq> instantiation_thy 
  where iof = iof
  by (unfold_locales ; blast)   

locale iso_universals = 
    iso_instantiation 
          where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u +
    universals 
          where iof = iof 
            and Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u 
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> and
    Typ\<^sub>u :: \<open>'u itself\<close> 
begin

lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_E[elim]:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  obtains f where 
    \<open>inj_on f \<P>\<close> \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>U \<in> \<U>\<close> 
    \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close>  
proof -
  obtain f where 
    A: \<open>inj_on f \<E>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> \<P>\<close> 
       \<open>zf_iof (MorphImg f \<Gamma>) (f x) (f ` w) U\<close>
    using assms iof_E1 by blast
  have B: \<open>U \<in> \<U>\<close> using assms by blast
  show ?thesis using A B that by metis
qed
      
lemma  \<^marker>\<open>tag (proof) aponly\<close> iof_scope:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>U \<in> \<U>\<close>   
  using assms by blast+
 
end 

end