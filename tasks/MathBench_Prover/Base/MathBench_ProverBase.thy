theory MathBench_ProverBase
  imports
    (* Transcendence — FIRST: its transitive dep on Jordan_Normal_Form
       introduces JNF's mat/row/vec/det; placing it first lets later
       HOL-Analysis imports shadow those names. *)
    Hermite_Lindemann.Hermite_Lindemann
    (* Tool infrastructure *)
    "HOL-Decision_Procs.Reflective_Field"
    (* Multivariate polynomials — early so later Polynomial imports shadow MPoly_Type names *)
    Power_Sum_Polynomials.Power_Sum_Polynomials
    (* HOL bundles *)
    "HOL-Library.Library"
    "HOL-Combinatorics.Combinatorics"
    (* Basic math *)
    "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
    Derangements.Derangements
    "Bell_Numbers_Spivey.Bell_Numbers"
    Card_Number_Partitions.Card_Number_Partitions
    Pell.Pell_Algorithm
    Lucas_Theorem.Lucas_Theorem
    "Budan_Fourier.Budan_Fourier"
    "Lifting_the_Exponent.LTE"
    "Bertrands_Postulate.Bertrand"
    (* Analysis / matrices *)
    "Gauss_Jordan.Determinants_IArrays"
    "Catalan_Numbers.Catalan_Numbers"
    Stirling_Formula.Stirling_Formula
    "Fourier.Fourier"
    (* Complex analysis / number theory *)
    Euler_MacLaurin.Euler_MacLaurin_Landau
    Chebyshev_Polynomials.Chebyshev_Polynomials
    Dirichlet_Series.Dirichlet_Series_Analysis
    Linear_Recurrences.Rational_FPS_Asymptotics
    Gaussian_Integers.Gaussian_Integers_Everything
    (* Polynomial root counting & factorization *)
    Count_Complex_Roots.Count_Complex_Roots
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
    (* ODE existence/uniqueness: Picard-Lindelöf, Grönwall *)
    Ordinary_Differential_Equations.ODE_Analysis
    (* Cayley-Hamilton theorem transferred to 'a^'n^'n *)
    Lie_Groups.Transfer_Cayley_Hamilton
    (* Exact real root counting (complements Budan_Fourier) *)
    Sturm_Sequences.Sturm_Method
    (* Roots of unity, DFT on finite groups *)
    Gauss_Sums.Complex_Roots_Of_Unity
    (* Falling factorial / Vandermonde identities *)
    Falling_Factorial_Sum.Falling_Factorial_Sum_Combinatorics
    (* Base-b digit representation *)
    DigitsInBase.DigitsInBase
    (* Continued fractions, best rational approximation, quadratic irrationals *)
    Continued_Fractions.Continued_Fractions
    (* Geometry of numbers: Minkowski's lattice point theorem *)
    Minkowskis_Theorem.Minkowskis_Theorem
    Gauss_Sums.Polya_Vinogradov
    Chord_Segments.Chord_Segments
    (* Zeckendorf representation of naturals as sums of non-consecutive Fibonacci numbers *)
    Zeckendorf.Zeckendorf
    (* Tarski plane geometry: IsaGeoCoq's axiomatic development (circles, circumcenter,
       concyclic, perpendicular bisector, two-circle intersection) together with
       Tarskis_Geometry's real^2 model (real_euclid: tarski), whose axioms A1-A11
       discharge IsaGeoCoq's Tarski_Euclidean_2D_Continuous locale on real^2. *)
    Tarskis_Geometry.Euclid_Tarski
    IsaGeoCoq.Tarski_Euclidean_2D_Continuous
    IsaGeoCoq.Highschool_Euclidean_2D
    (* Sophomores' dream integral identities; promoted by the missing-lemma
       loop (ml-0025/26/27 need sophomores_dream_aux_integral / _aux2 /
       integrable_sophomores_dream). Placed last so its HOL-Analysis content
       follows the geometry imports, matching the validated resolution. *)
    Sophomores_Dream.Sophomores_Dream
begin

(* Sophomores_Dream brings Abstract_Metric_Spaces.metric.metric into scope;
   for the short name `metric` Tarskis_Geometry.Metric.metric would shadow it,
   but PutnamBench resolves `metric` to the metric-space one. Hide the geometry
   constant (open) so the metric-space wins; qualified Metric.metric stays. *)
hide_const (open) Metric.metric

end