import RankTwoOriginalCover245212
import RankTwoCell6
import RankTwoCell7
import RankTwoCell8
import RankTwoCell9
import RankTwoCell10
import RankTwoCell11
import RankTwoCell12
import RankTwoCell13
import RankTwoCell14
import RankTwoCell15
import RankTwoCell16
import RankTwoCell17
import RankTwoCell18
import RankTwoCell19
import RankTwoCell20
import RankTwoCell21
import RankTwoCell22
import RankTwoCell23
import RankTwoCell24
import RankTwoCell25
import RankTwoCell26
import RankTwoCell27
import RankTwoCell28
import RankTwoCell29
import RankTwoCell30
import RankTwoCell31
import RankTwoCell32
/-! Join the existing independently checked arithmetic modules. -/
namespace OMA.RankTwoJoined245212
open OMA.RankTwoInteriorCover245212 OMA.RankTwoInteriorWalk245212
theorem roots (m : ℕ) (lo : 6 ≤ m) (hi : m ≤ 32) (swap : Bool) : Closed (root m 6 1250 swap) := by
  interval_cases m
  · cases swap
    · exact OMA.RankTwoCell6.normal
    · exact OMA.RankTwoCell6.reverse
  · cases swap
    · exact OMA.RankTwoCell7.normal
    · exact OMA.RankTwoCell7.reverse
  · cases swap
    · exact OMA.RankTwoCell8.normal
    · exact OMA.RankTwoCell8.reverse
  · cases swap
    · exact OMA.RankTwoCell9.normal
    · exact OMA.RankTwoCell9.reverse
  · cases swap
    · exact OMA.RankTwoCell10.normal
    · exact OMA.RankTwoCell10.reverse
  · cases swap
    · exact OMA.RankTwoCell11.normal
    · exact OMA.RankTwoCell11.reverse
  · cases swap
    · exact OMA.RankTwoCell12.normal
    · exact OMA.RankTwoCell12.reverse
  · cases swap
    · exact OMA.RankTwoCell13.normal
    · exact OMA.RankTwoCell13.reverse
  · cases swap
    · exact OMA.RankTwoCell14.normal
    · exact OMA.RankTwoCell14.reverse
  · cases swap
    · exact OMA.RankTwoCell15.normal
    · exact OMA.RankTwoCell15.reverse
  · cases swap
    · exact OMA.RankTwoCell16.normal
    · exact OMA.RankTwoCell16.reverse
  · cases swap
    · exact OMA.RankTwoCell17.normal
    · exact OMA.RankTwoCell17.reverse
  · cases swap
    · exact OMA.RankTwoCell18.normal
    · exact OMA.RankTwoCell18.reverse
  · cases swap
    · exact OMA.RankTwoCell19.normal
    · exact OMA.RankTwoCell19.reverse
  · cases swap
    · exact OMA.RankTwoCell20.normal
    · exact OMA.RankTwoCell20.reverse
  · cases swap
    · exact OMA.RankTwoCell21.normal
    · exact OMA.RankTwoCell21.reverse
  · cases swap
    · exact OMA.RankTwoCell22.normal
    · exact OMA.RankTwoCell22.reverse
  · cases swap
    · exact OMA.RankTwoCell23.normal
    · exact OMA.RankTwoCell23.reverse
  · cases swap
    · exact OMA.RankTwoCell24.normal
    · exact OMA.RankTwoCell24.reverse
  · cases swap
    · exact OMA.RankTwoCell25.normal
    · exact OMA.RankTwoCell25.reverse
  · cases swap
    · exact OMA.RankTwoCell26.normal
    · exact OMA.RankTwoCell26.reverse
  · cases swap
    · exact OMA.RankTwoCell27.normal
    · exact OMA.RankTwoCell27.reverse
  · cases swap
    · exact OMA.RankTwoCell28.normal
    · exact OMA.RankTwoCell28.reverse
  · cases swap
    · exact OMA.RankTwoCell29.normal
    · exact OMA.RankTwoCell29.reverse
  · cases swap
    · exact OMA.RankTwoCell30.normal
    · exact OMA.RankTwoCell30.reverse
  · cases swap
    · exact OMA.RankTwoCell31.normal
    · exact OMA.RankTwoCell31.reverse
  · cases swap
    · exact OMA.RankTwoCell32.normal
    · exact OMA.RankTwoCell32.reverse
open scoped ArithmeticFunction.sigma
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13 ≤ p) (pq : p < q) (ha : 5 ≤ a) (hd : 5 ≤ d) :
    OeisA245212.a (2^k*p^a*q^d) ≠ (σ 1 (2^k*p^a*q^d):ℤ) :=
  OMA.RankTwoOriginalCover245212.of_roots roots hp hq op pq ha hd
#print axioms original
end OMA.RankTwoJoined245212
