
section \<open>Object-Free Categories\<close>

theory LR_Semigroup
  imports Main

begin

notation times (infixl "\<cdot>" 70) 

subsection \<open>Relational Magmas and LR-Magmas\<close>

class relational_magma =
  fixes \<rho> ::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>bool"

begin

definition "\<Delta> x y = (\<exists>z. \<rho> z x y)"

definition "unitl e = ((\<exists>x. \<rho> x e x) \<and> (\<forall>x y. \<rho> y e x \<longrightarrow> y = x))"

definition "unitr e = ((\<exists>x. \<rho> x x e) \<and> (\<forall>x y. \<rho> y x e \<longrightarrow> y = x))"

abbreviation "unit e \<equiv> (unitl e \<or> unitr e)"

end

class unital_relational_magma = relational_magma +
  assumes unitl_ex: "\<forall>x.\<exists>e. unitl e \<and> \<Delta> e x"
  and unitr_ex: "\<forall>x.\<exists>e. unitr e \<and> \<Delta> x e"

begin

lemma unitl_idem: "unitl e \<Longrightarrow> \<rho> e e e"
proof-
  assume hyp: "unitl e"
  have "\<exists>e'. unitr e' \<and> \<Delta> e e'"
    using local.unitr_ex by auto
  hence "\<exists>e' z. unitr e' \<and> \<rho> z e e'"
    by (simp add: local.\<Delta>_def)
  hence "\<exists>e' z. unitr e' \<and> \<rho> z e e' \<and> z = e \<and> z = e'"
    using hyp local.unitl_def local.unitr_def by blast
  thus "\<rho> e e e"
    by simp
qed

lemma unitr_idem: "unitr e \<Longrightarrow> \<rho> e e e"
  by (metis local.\<Delta>_def local.unitl_def local.unitl_ex relational_magma.unitr_def)

lemma unit_idem: "unit e \<Longrightarrow> \<rho> e e e"
  using unitl_idem unitr_idem by blast

lemma unit_D: "unit e \<Longrightarrow> \<Delta> e e"
  using local.\<Delta>_def unit_idem by blast

lemma units_eq: "unit e\<^sub>1 \<Longrightarrow> unit e\<^sub>2 \<Longrightarrow> \<Delta> e\<^sub>1 e\<^sub>2 \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
proof-
  assume hyp1: "unit e\<^sub>1"
  and hyp2: "unit e\<^sub>2"
  and hyp3: "\<Delta> e\<^sub>1 e\<^sub>2"
  hence "\<exists>x. \<rho> x e\<^sub>1 e\<^sub>2"
    by (simp add: local.\<Delta>_def)
  hence "\<exists>x. \<rho> x e\<^sub>1 e\<^sub>2 \<and> x = e\<^sub>1 \<and> x = e\<^sub>2"
    by (metis hyp1 hyp2 local.\<Delta>_def local.unitl_def local.unitl_ex local.unitr_def local.unitr_ex)
  thus "e\<^sub>1 = e\<^sub>2"
    by blast
qed

lemma units_iff: "unit e\<^sub>1 \<Longrightarrow> unit e\<^sub>2 \<Longrightarrow> (\<Delta> e\<^sub>1 e\<^sub>2 = (e\<^sub>1 = e\<^sub>2))"
  using unit_D units_eq by blast

end

class LR_magma = relational_magma + 
fixes so :: "'a \<Rightarrow> 'a"
  and ta :: "'a \<Rightarrow> 'a"
  assumes Dlr: "\<Delta> x y \<Longrightarrow> (ta x = so y)"
  and l_absorb: "\<rho> x (so x) x" 
  and r_absorb: "\<rho> x x (ta x)"
  and l_absorb_eq: "\<rho> y (so x) x \<Longrightarrow> x = y" 
  and r_absorb_eq: "\<rho> y x (ta x) \<Longrightarrow> x = y"

begin

lemma lr_closed [simp]: "ta (so x) = so x"
proof-
  have "\<rho> x (so x) x"
    using local.l_absorb by force
  hence "\<Delta> (so x) x"
    using local.\<Delta>_def by blast
  thus ?thesis
    by (simp add: local.Dlr)
qed 

lemma rl_closed [simp]: "so (ta x) = ta x"
  by (metis local.Dlr local.\<Delta>_def local.r_absorb)

lemma l_idem [simp]: "so (so x) = so x"
proof-
  have "so (so x) = so (ta (so x))"
    by simp
  also have "\<dots> = ta (so x)"
    using rl_closed by blast
  also have "\<dots> = so x"
    by simp
  finally show ?thesis.
qed

lemma r_idem [simp]: "ta (ta x) = ta x"
  by (metis lr_closed rl_closed)

lemma LR_fix: "(ta x = x) = (so x = x)"
  by (metis local.lr_closed local.rl_closed)

lemma lr_fix: "{x. so x = x} = {x. ta x = x}"
  by (simp add: LR_fix)

lemma l_idem_var: "\<rho> (so x) (so x) (so x)"
proof-
  have "\<rho> (so x) (so (so x)) (so x)"
    using local.l_absorb by blast
  thus ?thesis
    by simp
qed

lemma r_idem_var: "\<rho> (ta x) (ta x) (ta x)"
  by (metis local.l_absorb rl_closed)

lemma lr_comm: "\<rho> v (ta x) (so y) \<Longrightarrow> \<rho> w (so y) (ta x) \<Longrightarrow> v = w"
proof-
  assume h1: "\<rho> v (ta x) (so y)"  
  and h2: "\<rho> w (so y) (ta x)"
  hence "ta (ta x) = so (so y)"
    using local.Dlr local.\<Delta>_def by blast
  hence b: "ta x = so y"
    by simp
  hence c: "v = ta x"
    by (metis h1 local.r_absorb_eq lr_closed)
  hence "w = ta x"
    by (metis b h2 local.r_absorb_eq r_idem)
  thus ?thesis
    by (simp add: c)
qed

lemma lr_comm_var: "\<rho> v (ta x) (so y) = \<rho> v (so y) (ta x)"
  using local.Dlr local.\<Delta>_def by force

lemma l_weak_twisted: "\<rho> u x y \<Longrightarrow> \<rho> v (so u) x \<Longrightarrow> \<rho> v x (so y)"
proof-
  assume h1: "\<rho> u x y"
  and h2: "\<rho> v (so u) x"
  hence a: "ta x = so y"
    using local.Dlr local.\<Delta>_def by blast
  hence "so u = so x"
    using h2 local.Dlr local.\<Delta>_def by fastforce
  hence "v = x"
    using h2 local.l_absorb_eq by auto
  thus ?thesis
    by (metis a local.r_absorb)
qed

lemma r_weak_twisted: "\<rho> u x y \<Longrightarrow>  \<rho> v y (ta u) \<Longrightarrow> \<rho> v (ta x) y"
  by (metis local.Dlr local.\<Delta>_def local.l_absorb local.r_absorb_eq rl_closed)

lemma l_comm_var: "\<rho> v (so x) (so y) = \<rho> v (so y) (so x)"
  using local.Dlr relational_magma.\<Delta>_def by fastforce

lemma r_comm_var: "\<rho> v (ta x) (ta y) = \<rho> v (ta y) (ta x)"
  by (metis local.l_comm_var rl_closed)

lemma l_export: "\<rho> u (so x) y \<Longrightarrow> \<rho> v (so x) (so y) \<Longrightarrow> so u = v"
  by (metis local.Dlr local.\<Delta>_def local.l_absorb_eq lr_closed)

lemma r_export: "\<rho> u x (ta y) \<Longrightarrow> \<rho> v (ta x) (ta y) \<Longrightarrow> ta u = v"
  by (metis local.Dlr local.\<Delta>_def local.r_absorb_eq rl_closed)

lemma "\<rho> x (so y) z \<Longrightarrow> so y = so z"
  using local.Dlr local.\<Delta>_def by fastforce

lemma "\<rho> x (so y) z \<Longrightarrow> \<exists>w. \<rho> w (so y) (so z)"
  using l_idem_var local.Dlr local.\<Delta>_def by fastforce
  
lemma "\<rho> x y (ta z) \<Longrightarrow> ta y = ta z"
  using local.Dlr local.\<Delta>_def by fastforce

lemma "\<rho> w y z \<Longrightarrow> \<rho> x y z \<Longrightarrow> w = x"
  nitpick
  oops

lemma "\<rho> v x y \<Longrightarrow> \<Delta> y z \<Longrightarrow> \<Delta> v z"
  nitpick
  oops

lemma "(\<forall>x y. ta x = so y \<longrightarrow> \<Delta> x y) \<Longrightarrow> (\<forall>v x y z. \<rho> v x y \<longrightarrow> \<Delta> y z \<longrightarrow> \<Delta> v z)"
  nitpick
  oops

end

sublocale LR_magma \<subseteq> rmc2: unital_relational_magma
  apply unfold_locales
  apply (metis local.Dlr local.\<Delta>_def local.l_absorb local.l_absorb_eq local.unitl_def)
  by (metis local.Dlr local.r_absorb local.r_absorb_eq local.unitr_def relational_magma.\<Delta>_def)

class coherent_relational_magma = relational_magma +
  assumes coherence: "\<rho> v x y \<Longrightarrow> \<Delta> y z \<Longrightarrow> \<Delta> v z"

class coherent_LR_magma = LR_magma +
  assumes lr_coherence: "ta x = so y \<Longrightarrow> \<Delta> x y"

begin

lemma coherence_eq: "\<Delta> x y = (ta x = so y)"
  using local.Dlr local.lr_coherence by blast

lemma "\<rho> w y z \<Longrightarrow> \<rho> x y z \<Longrightarrow> w = x"
  nitpick
  oops

end

subsection \<open>Partial Magmas\<close>

text \<open>Partial magmas are functional relational magmas.\<close>

class partial_magma = relational_magma +
  assumes functionality: "\<rho> w y z \<Longrightarrow> \<rho> x y z \<Longrightarrow> w = x"

begin

lemma "\<rho> v x y \<Longrightarrow> \<Delta> y z \<Longrightarrow> \<Delta> v z"
  nitpick
  oops

definition pcomp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70) where
  "x \<otimes> y = (THE z. \<rho> z x y)"

lemma functionality_var: "\<Delta> x y \<Longrightarrow> (\<exists>!z. \<rho> z x y)"
  using local.\<Delta>_def local.functionality by blast

lemma functionality_lem: "(\<exists>!z. \<rho> z x y) \<or> \<not>(\<Delta> x y)"
  using functionality_var by blast

lemma pcomp_def_var: "(\<Delta> x y \<and> x \<otimes> y = z) = \<rho> z x y"
  by (metis functionality_var pcomp_def relational_magma.\<Delta>_def the_equality)

lemma pcomp_def_var2: "\<Delta> x y \<Longrightarrow> ((x \<otimes> y = z) = \<rho> z x y)"
  using pcomp_def_var by blast

end

class unital_partial_magma = partial_magma + unital_relational_magma

begin

lemma p_unitl_ex: "\<forall>x.\<exists>e. unit e \<and> \<Delta> e x \<and> e \<otimes> x = x"
  by (metis (full_types) local.pcomp_def_var2 local.unitl_ex relational_magma.unitl_def)

lemma  p_unitr_ex: "\<forall>x.\<exists>e. unit e \<and> \<Delta> x e \<and> x \<otimes> e = x"
  by (metis (full_types) local.pcomp_def_var2 local.unitr_ex relational_magma.unitr_def)

lemma p_unit_idem: "unit e \<Longrightarrow> e \<otimes> e = e"
  using local.units_eq p_unitr_ex by blast

end

class partial_LR_magma = LR_magma + partial_magma


subsection \<open>Relational Semigroups\<close>

class relational_semigroup = relational_magma +
  assumes rel_assoc: "(\<exists>y. \<rho> y u v \<and> \<rho> x y w) = (\<exists>z. \<rho> z v w \<and> \<rho> x u z)"

class partial_semigroup = relational_semigroup + partial_magma

begin

text \<open>We verify the algebraic partial semigroup axioms. \<close>

lemma pcomp_assoc_delta: "(\<Delta> u v \<and> \<Delta> (u \<otimes> v) w) = (\<Delta> u (v \<otimes> w) \<and> \<Delta> v w)"
proof-
  have "(\<Delta> u v \<and> \<Delta> (u \<otimes> v) w) = (\<exists>x. \<Delta> u v \<and> \<Delta> x w \<and> x = u \<otimes> v)"
    by simp
  also have "\<dots> = (\<exists>x. \<rho> x u v \<and> \<Delta> x w)"
    by (metis local.pcomp_def_var)
  also have "\<dots> = (\<exists>x. \<rho> x v w \<and> \<Delta> u x)"
    by (meson local.pcomp_def_var local.rel_assoc)
  also have "\<dots> = (\<exists>x. \<Delta> v w \<and> x = v \<otimes> w \<and> \<Delta> u x)"
    by (metis local.pcomp_def_var)
  also have "\<dots> = (\<Delta> u (v \<otimes> w) \<and> \<Delta> v w)"
    by auto 
  finally show ?thesis.
qed

lemma pcomp_assoc_prod: "\<Delta> x y \<and> \<Delta> (x \<otimes> y) z \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  by (smt local.functionality_var local.pcomp_def_var local.rel_assoc)

end

class coherent_relational_semigroup = relational_semigroup + coherent_relational_magma

class of_semicategory = coherent_relational_semigroup + partial_semigroup

begin

lemma part_coherence: "\<Delta> x y \<Longrightarrow> \<Delta> y z \<Longrightarrow> \<Delta> (x \<otimes> y) z"
  using local.coherence local.pcomp_def_var by blast

lemma coherence_iff: "(\<Delta> x y \<and> \<Delta> y z) = (\<Delta> x y \<and> \<Delta> (x \<otimes> y) z)"
  using local.pcomp_assoc_delta part_coherence by blast

end


subsection \<open>Relational Monoids\<close>

class relational_monoid = relational_semigroup + unital_relational_magma

begin

lemma units_uniquel: "\<forall>x.\<exists>!e. unit e \<and> \<rho> x e x"

  by (metis local.\<Delta>_def local.rel_assoc local.unitl_ex local.units_eq relational_magma.unitl_def)

lemma units_uniquer: "\<forall>x.\<exists>!e. unit e \<and> \<rho> x x e"
  by (metis (no_types, hide_lams) local.\<Delta>_def local.rel_assoc local.unitl_ex local.unitr_ex relational_magma.unitl_def relational_magma.unitr_def)

lemma units_unique: "(\<forall>x y. \<Delta> x y) \<Longrightarrow> \<exists>!e. unit e"
  using local.unitl_ex local.units_iff by auto

text \<open>Next we define source and target operations.\<close>

definition source :: "'a \<Rightarrow> 'a" where
  "source x = (THE e. unit e \<and> \<rho> x e x)"

definition target :: "'a \<Rightarrow> 'a" where
  "target x = (THE e. unit e \<and> \<rho> x x e)"

text \<open>We can now verify the axioms of f-systems and lr-semigroups, as well as additional properties.\<close>

lemma source_unit: "unit (source x)"
  unfolding source_def by (metis (mono_tags, lifting) theI' units_uniquel)

lemma target_unit: "unit (target x)"
  unfolding target_def by (metis (mono_tags, lifting) theI' units_uniquer)

lemma source_absorbl: "\<rho> x (source x) x"
  unfolding source_def by (smt theI' units_uniquel) 

lemma target_absorbr: "\<rho> x x (target x)"
  unfolding target_def by (smt theI units_uniquer)

lemma source_target_Def: "\<Delta> x y \<Longrightarrow> target x = source y"
  by (metis (mono_tags) local.rel_assoc local.unitr_ex local.units_eq relational_magma.\<Delta>_def source_absorbl source_unit target_absorbr target_unit)

text \<open>Units can now be characterised as fixpoints.\<close>

lemma unitl_source: "unitl x = (source x = x)"
  by (metis (full_types) local.unitl_ex local.unitl_idem local.units_eq source_absorbl source_unit units_uniquel)

lemma unitr_target: "unitr x = (target x = x)"
  by (metis (full_types) local.unitl_ex local.unitr_ex local.units_eq relational_magma.unitl_def target_absorbr target_unit)

text \<open>The following statements formalise equivalent properties of coherence.\<close>

lemma coherent1: "(\<forall>v x y z. \<rho> v x y \<longrightarrow> \<Delta> y z \<longrightarrow> \<Delta> v z) = (\<forall>e x y. unit e \<longrightarrow> \<rho> x x e \<longrightarrow> \<rho> y e y \<longrightarrow> \<Delta> x y)"
  apply standard
  using local.\<Delta>_def apply blast
  by (metis local.\<Delta>_def local.rel_assoc source_absorbl source_target_Def target_absorbr unitr_target)

lemma coherent2: "(\<forall>e x y. unit e \<longrightarrow> \<rho> x x e \<longrightarrow> \<rho> y e y \<longrightarrow> \<Delta> x y) = (\<forall>x y. target x = source y \<longrightarrow> \<Delta> x y)"
  apply standard
  apply (metis source_absorbl source_unit target_absorbr)
  by (metis (full_types) local.unit_D relational_magma.\<Delta>_def source_target_Def)

end

class partial_monoid = relational_monoid + partial_magma

begin

text \<open>Using the syntax for definedness and composition in partial monoids, we
can now derive algebraic versions of the relational properties above.\<close>

lemma alg_units_uniquel: "\<forall>x.\<exists>!e. unit e \<and> \<Delta> e x \<and> e \<otimes> x = x"
  by (simp add: local.pcomp_def_var units_uniquel)

lemma alg_units_uniquer: "\<forall>x.\<exists>!e. unit e \<and> \<Delta> x e \<and> x \<otimes> e = x"
  by (simp add: local.pcomp_def_var units_uniquer)

end

class coherent_relational_monoid = relational_monoid + coherent_relational_magma

begin

text \<open>The following statements formalise again coherence properties.\<close>

lemma coherence_conv: "\<rho> v x y \<Longrightarrow> (\<Delta> v z = \<Delta> y z)"
  by (metis (full_types) local.coherence local.rel_assoc relational_magma.\<Delta>_def)

lemma coherence_alt: "unit e \<Longrightarrow> \<rho> x x e \<Longrightarrow> \<rho> y e y \<Longrightarrow> \<Delta> x y"
  using coherence_conv local.\<Delta>_def by blast

lemma coherence_iff: "\<Delta> x y = (\<exists>e. unit e \<and> \<Delta> x e \<and> \<Delta> e y)"
  by (metis coherence_conv local.source_target_Def local.target_absorbr local.unitl_ex local.units_eq)

lemma coherence_conv2: "target x = source y \<Longrightarrow> \<Delta> x y"
  using coherence_alt local.coherent2 by blast

lemma coherence_iff2: "(target x = source y) = \<Delta> x y"
  using coherence_alt local.coherent2 local.source_target_Def by blast

end

class of_category = of_semicategory + partial_monoid


subsection \<open>Relational LR-Semigroups\<close>

class LR_semigroup = LR_magma + relational_semigroup

sublocale relational_monoid \<subseteq> rmc: LR_semigroup _  source target
  apply unfold_locales
      apply (simp_all add: source_absorbl target_absorbr \<Delta>_def source_target_Def)
   apply (metis local.source_target_Def local.source_unit local.unit_D local.unitl_source local.unitr_target relational_magma.unitl_def)
  by (metis local.source_target_Def local.target_unit local.unit_D local.unitr_target relational_magma.\<Delta>_def relational_magma.unitr_def)

sublocale LR_semigroup \<subseteq> rmc22: relational_monoid..

sublocale monoid_mult \<subseteq> mmlr: LR_semigroup "\<lambda>x y z. x = y \<cdot> z" "\<lambda>x. 1" "\<lambda>y. 1"
  by unfold_locales (simp_all add: mult_assoc)


context LR_semigroup
begin

lemma l_strong_local: "\<rho> v x y \<Longrightarrow> so v = so x"
proof-
  assume hyp: "\<rho> v x y"
  hence "\<rho> v (so v) v \<and> \<rho> v x y"
    by (simp add: local.l_absorb)
  hence "\<exists>w. \<rho> w (so v) x \<and> \<rho> v w y"
    using local.rel_assoc by blast
  hence "ta (so v) = so x"
    using local.Dlr local.\<Delta>_def by blast
  thus ?thesis
    by simp
qed

lemma r_strong_local: "\<rho> v x y \<Longrightarrow> ta v = ta y"
  by (metis local.Dlr local.r_absorb local.rel_assoc relational_magma.\<Delta>_def)

lemma l_local: "\<rho> v x y \<Longrightarrow> \<rho> w x (so y) \<Longrightarrow> so v = so w"
  by (simp add: l_strong_local)

lemma r_local: "\<rho> v x y \<Longrightarrow> \<rho> w (ta x) y \<Longrightarrow> ta v = ta w"
  by (simp add: r_strong_local)

lemma r_twisted: "\<rho> u x y \<Longrightarrow> (\<rho> v (ta x) y = \<rho> v y (ta u))"
  apply standard
proof -
  assume a1: "\<rho> u x y"
  assume "\<rho> v (ta x) y"
  then have "v = y"
    using local.Dlr local.\<Delta>_def local.l_absorb_eq by force
  then show "\<rho> v y (ta u)"
    using a1 local.r_absorb r_strong_local by presburger
next
  assume h1: "\<rho> u x y"
  and "\<rho> v y (ta u)"
  thus "\<rho> v (ta x) y"
    using local.r_weak_twisted by auto
qed

lemma l_twisted: "\<rho> u x y \<Longrightarrow> (\<rho> v x (so y) = \<rho> v (so u) x)"
  apply standard
  apply (metis l_strong_local local.Dlr local.l_absorb local.r_absorb_eq relational_magma.\<Delta>_def)
  by (simp add: local.l_weak_twisted)

lemma "\<rho> x y z \<Longrightarrow> \<rho> x' y z \<Longrightarrow> so x = so x'"
  by (simp add: l_strong_local)

lemma coherence_iff: "(\<forall>x y. \<Delta> x y = (ta x = so y)) = (\<forall>v x y z. \<rho> v x y \<longrightarrow> \<Delta> y z \<longrightarrow> \<Delta> v z)"
  apply standard
  apply (simp add: r_strong_local)
  by (metis local.Dlr local.r_absorb local.rmc2.unitl_ex relational_magma.unitl_def)
 
end

class coherent_LR_semigroup = LR_semigroup + coherent_LR_magma

begin

lemma "\<rho> v x y \<Longrightarrow> \<Delta> y z \<Longrightarrow> \<Delta> v z"
  by (simp add: local.coherence_eq local.r_strong_local)

end

class partial_LR_semigroup = LR_semigroup + partial_semigroup

begin

lemma pl_absorb [simp]: "so x \<otimes> x = x"
  using local.l_absorb local.pcomp_def_var by auto

lemma pr_absorb [simp]: "x \<otimes> ta x = x"
  using local.pcomp_def_var local.r_absorb by auto

end

class LR_category = coherent_LR_semigroup + partial_semigroup

begin

lemma pl_local: "ta x = so y \<Longrightarrow> so (x \<otimes> y) = so x"
  using local.coherence_eq local.l_strong_local local.pcomp_def_var2 by blast

lemma pr_local: "ta x = so y \<Longrightarrow> ta (x \<otimes> y) = ta y"
  using local.coherence_eq local.pcomp_def_var2 local.r_strong_local by blast

lemma p_assoc: "ta x = so y \<Longrightarrow> ta y = so z \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  by (simp add: local.coherence_eq local.pcomp_assoc_prod pr_local)

end

sublocale LR_category \<subseteq> lrof: of_category
  by unfold_locales (simp add: local.coherence_eq local.r_strong_local)

sublocale of_category \<subseteq> oflr: LR_category _ source target
  apply unfold_locales
  using local.coherence local.coherent1 local.coherent2 by blast

text \<open>The next two sublocale statements relate coherent relational monoids and LR-semigroups.\<close>

class LR_cat2 = partial_magma +
fixes l :: "'a \<Rightarrow> 'a"
  and r :: "'a \<Rightarrow> 'a"
  assumes Dlr: "\<Delta> x y = (r x = l y)"
  and lr_clo [simp]: "r (l x) = l x"
  and rl_clo [simp]: "l (r x) = r x"
  and l_abs [simp]: "l x \<otimes> x = x" 
  and r_abs [simp]: "x \<otimes> r x = x"
  and l_loc: "r x = l y \<Longrightarrow> l (x \<otimes> y) = l x"
  and r_loc: "r x = l y \<Longrightarrow> r (x \<otimes> y) = r y"
  and assoc: "r x = l y \<Longrightarrow> r y = l z \<Longrightarrow> x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"

begin

lemma assoc_def: "(\<Delta> u v \<and> \<Delta> (u \<otimes> v) w) = (\<Delta> u (v \<otimes> w) \<and> \<Delta> v w)"
  using local.Dlr local.l_loc local.r_loc by auto

end

sublocale LR_cat2 \<subseteq> lrred1: LR_category _ l r
  apply unfold_locales
        apply (simp_all add: local.Dlr)
  using local.Dlr local.l_abs local.lr_clo local.pcomp_def_var apply blast
  using local.Dlr local.pcomp_def_var apply fastforce
  using local.pcomp_def_var apply force+
  by (smt local.Dlr local.assoc local.assoc_def local.pcomp_def_var)

sublocale LR_category \<subseteq> lrrde2: LR_cat2 _ so ta
  apply unfold_locales
         apply (simp_all add: pl_local pr_local p_assoc coherence_eq)
  using local.l_absorb local.pcomp_def_var apply blast
  using local.pcomp_def_var local.r_absorb by blast

text \<open>The next two sublocale statements relate object_free categories and LR-categories.\<close>

sublocale of_category \<subseteq> ofrl1: LR_cat2 _ source target ..

sublocale LR_cat2 \<subseteq> ofrl2: of_category..

subsection \<open>Categories\<close>

locale category = 
  fixes id :: "'objects \<Rightarrow> 'arrows"
  and dom :: "'arrows \<Rightarrow> 'objects"
  and cod :: "'arrows \<Rightarrow> 'objects"
  and comp :: "'arrows \<Rightarrow> 'arrows \<Rightarrow> 'arrows" (infixl "\<odot>" 70)
assumes dom_id [simp]: "dom (id X) = X"
and cod_id [simp]: "cod (id X) = X"
and id_dom [simp]: "id (dom f) \<odot> f = f"
and id_cod [simp]: "f \<odot> id (cod f) = f"
and dom_loc [simp]: "cod f = dom g \<Longrightarrow> dom (f \<odot> g) = dom f"
and cod_loc [simp]: "cod f = dom g \<Longrightarrow> cod (f \<odot> g) = cod g"
and assoc: "cod f = dom g \<Longrightarrow> cod g = dom h \<Longrightarrow> (f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"

begin

lemma "cod f = dom g \<Longrightarrow> dom (f \<odot> g) = dom (f \<odot> id (dom g))"
  by simp

abbreviation "Lc f \<equiv> id (dom f)"

abbreviation "Rc f \<equiv> id (cod f)"

abbreviation "Rel \<equiv> \<lambda>f g h. Rc g = Lc h \<and> f = g \<odot> h"

end

sublocale category \<subseteq> catlr: LR_category Rel Lc Rc
  apply unfold_locales
         apply simp_all
  apply (simp add: relational_magma.\<Delta>_def)
   apply (metis cod_loc dom_id dom_loc local.assoc)
  by (simp add: relational_magma.\<Delta>_def)

typedef (overloaded) 'a lr_objects = "{(x::'a::LR_category). so x = x}"
  by (meson mem_Collect_eq rl_closed)

setup_lifting type_definition_lr_objects

lemma Lfix_coerce [simp]: "Abs_lr_objects (so (Rep_lr_objects X)) = X"
  by (metis (mono_tags, lifting) CollectD Rep_lr_objects Rep_lr_objects_inverse)

lemma Rfix_coerce [simp]: "Abs_lr_objects (ta (Rep_lr_objects X)) = X"
  by (metis (mono_tags, lifting) CollectD Rep_lr_objects Rep_lr_objects_inverse lr_closed)

(*sublocale LR_category \<subseteq> lrcat: category Rep_lr_objects "Abs_lr_objects \<circ> L" "Abs_lr_objects \<circ> R" "(\<otimes>)"
  apply unfold_locales
        apply (simp_all add: Abs_lr_objects_inverse Abs_lr_objects_inject)
    apply (simp add: LR_category_class.LR_dom_local)
   apply (simp add: LR_category_class.LR_cod_local)
  by (simp add: LR_category_class.LR_assoc)*)



subsection \<open>f-Systems\<close>

class f_system = semigroup_mult +
  fixes L :: "'a \<Rightarrow> 'a"
  and R :: "'a \<Rightarrow> 'a"
assumes f1: "L (R x) = R x"
and f2: "R (L x) = L x"
and f3: "L x \<cdot> x = x"
and f4: "x \<cdot> R x = x"
and f5: "L (x \<cdot> y) = L (x \<cdot> L y)"
and f6: "R (x \<cdot> y) = R (R x \<cdot> y)"
and f7: "L x \<cdot> R y = R y \<cdot> L x"
and f8: "R x \<cdot> y = y \<cdot> R (x \<cdot> y)"

begin

lemma "L (x \<cdot> y) = L x"
  nitpick
  oops


end

subsection \<open>Zero\<close>

class relational_magma_zero = relational_magma + zero +
  assumes zerol: "\<rho> 0 0 x"
  and zeror: "\<rho> 0 x 0"

class relational_semigroup_zero = relational_semigroup + relational_magma_zero

begin

lemma rel_semigroup_total: "\<Delta> x y"
proof-
  have "\<rho> 0 x 0 \<and> \<rho> 0 y 0"
    by (simp add: local.zeror)
  hence "\<exists>z. \<rho> 0 x z \<and> \<rho> z y 0"
    by blast
  hence "\<exists>z. \<rho> 0 z 0 \<and> \<rho> z x y"
    using local.rel_assoc by blast
  thus "\<Delta> x y"
    using local.\<Delta>_def by blast
qed

end

class relational_monoid_zero = relational_monoid + relational_magma_zero

begin

text \<open>The next statements yield weak notions of unit.\<close>

lemma "unitl e \<Longrightarrow> (\<exists>x. \<rho> x e x) \<and> (\<forall>x. \<rho> x e x \<or> \<rho> 0 e x)"
  using local.units_uniquel local.zeror by blast

lemma "unitr e \<Longrightarrow> (\<exists>x. \<rho> x x e) \<and> (\<forall>x. \<rho> x x e \<or> \<rho> 0 x e)"
  by (metis local.units_uniquel local.units_uniquer local.zeror)

text \<open>The next statement shows that every relational monoid with zero has one single unit.\<close>

lemma "unit e \<Longrightarrow> unit e' \<Longrightarrow> D e e'\<Longrightarrow> e = e'"
  using local.units_uniquel local.zeror by auto

lemma "\<exists>!e. unit e"
  using local.units_uniquer local.zerol by blast

end

class partial_monoid_zero = relational_monoid_zero + partial_monoid

begin

lemma "unit 0"
  nitpick
  oops

lemma "\<not> unit 0"
  nitpick
  oops

lemma "\<rho> x 0 y \<Longrightarrow> x = 0"
  by (simp add: local.functionality local.zerol)

end

end