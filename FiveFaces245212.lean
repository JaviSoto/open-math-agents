import FiveFaceCore245212

namespace OMA.FiveFace245212
open OMA.Smooth245212
set_option maxHeartbeats 15000000
set_option maxRecDepth 60000
theorem face5l : Good (85/54:ℚ) 7 11 ⟨1,some 3⟩ ⟨1,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rl : Good (85/54:ℚ) 7 11 ⟨4,none⟩ ⟨1,some 3⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrl : Good (85/54:ℚ) 7 11 ⟨4,some 9⟩ ⟨4,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrl : Good (85/54:ℚ) 7 11 ⟨10,none⟩ ⟨4,some 9⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrll : Good (85/54:ℚ) 7 11 ⟨10,some 21⟩ ⟨10,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrlrl : Good (85/54:ℚ) 7 11 ⟨10,some 13⟩ ⟨22,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrlrrl : Good (85/54:ℚ) 7 11 ⟨14,some 21⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.fst 16 .leaf (.snd 29 .leaf (.fst 18 .leaf (.snd 36 .leaf (.fst 19 .leaf (.snd 40 .leaf (.fst 20 .leaf (.snd 42 (.snd 41 .leaf .leaf) .leaf)))))))) (by decide +kernel)
theorem face5rrrrlrrrl : Good (85/54:ℚ) 7 11 ⟨14,some 16⟩ ⟨46,none⟩ := sound (by norm_num) (by decide) (by decide) (.snd 93 .leaf (.fst 14 .leaf (.snd 189 .leaf (.fst 15 .leaf (.snd 381 .leaf (.snd 765 .leaf (.snd 1533 (.snd 1021 (.snd 875 (.snd 816 (.snd 790 (.snd 777 (.snd 771 .leaf (.snd 774 .leaf (.snd 775 .leaf (.snd 776 .leaf .leaf)))) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))))))) (by decide +kernel)
theorem face5rrrrlrrrrl : Good (85/54:ℚ) 7 11 ⟨17,some 21⟩ ⟨46,some 93⟩ := sound (by norm_num) (by decide) (by decide) (.fst 18 (.snd 61 .leaf (.snd 74 .leaf (.fst 17 .leaf (.snd 83 .leaf (.snd 88 (.snd 85 (.snd 84 .leaf .leaf) .leaf) .leaf))))) (.snd 61 (.fst 19 .leaf (.snd 52 (.fst 20 (.snd 48 .leaf .leaf) .leaf) .leaf)) .leaf)) (by decide +kernel)
theorem face5rrrrlrrrrr : Good (85/54:ℚ) 7 11 ⟨17,some 21⟩ ⟨94,none⟩ := sound (by norm_num) (by decide) (by decide) (.fst 18 (.snd 189 (.snd 125 (.fst 17 .leaf .leaf) (.fst 17 (.snd 151 (.snd 137 .leaf (.snd 144 .leaf (.snd 147 (.snd 145 .leaf (.snd 146 .leaf .leaf)) .leaf))) .leaf) .leaf)) .leaf) .leaf) (by decide +kernel)
theorem face5rrrrlrrrr : Good (85/54:ℚ) 7 11 ⟨17,some 21⟩ ⟨46,none⟩ := second (c:=93) face5rrrrlrrrrl face5rrrrlrrrrr
theorem face5rrrrlrrr : Good (85/54:ℚ) 7 11 ⟨14,some 21⟩ ⟨46,none⟩ := first (c:=16) face5rrrrlrrrl face5rrrrlrrrr
theorem face5rrrrlrr : Good (85/54:ℚ) 7 11 ⟨14,some 21⟩ ⟨22,none⟩ := second (c:=45) face5rrrrlrrl face5rrrrlrrr
theorem face5rrrrlr : Good (85/54:ℚ) 7 11 ⟨10,some 21⟩ ⟨22,none⟩ := first (c:=13) face5rrrrlrl face5rrrrlrr
theorem face5rrrrl : Good (85/54:ℚ) 7 11 ⟨10,some 21⟩ ⟨10,none⟩ := second (c:=21) face5rrrrll face5rrrrlr
theorem face5rrrrrlll : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrrllrl : Good (85/54:ℚ) 7 11 ⟨22,some 29⟩ ⟨14,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrrllrrl : Good (85/54:ℚ) 7 11 ⟨30,some 45⟩ ⟨14,some 16⟩ := sound (by norm_num) (by decide) (by decide) (.fst 36 .leaf (.fst 40 (.snd 14 .leaf (.snd 15 .leaf (.fst 38 .leaf (.fst 39 .leaf .leaf)))) (.snd 14 .leaf (.snd 15 (.fst 42 .leaf (.fst 43 .leaf .leaf)) .leaf)))) (by decide +kernel)
theorem face5rrrrrllrrr : Good (85/54:ℚ) 7 11 ⟨30,some 45⟩ ⟨17,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.fst 36 (.snd 18 (.fst 32 .leaf (.fst 34 .leaf (.snd 17 .leaf .leaf))) (.fst 32 (.snd 19 .leaf (.fst 30 (.snd 20 .leaf .leaf) (.snd 20 (.fst 31 .leaf .leaf) .leaf))) .leaf)) .leaf) (by decide +kernel)
theorem face5rrrrrllrr : Good (85/54:ℚ) 7 11 ⟨30,some 45⟩ ⟨14,some 21⟩ := second (c:=16) face5rrrrrllrrl face5rrrrrllrrr
theorem face5rrrrrllr : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨14,some 21⟩ := first (c:=29) face5rrrrrllrl face5rrrrrllrr
theorem face5rrrrrll : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨10,some 21⟩ := second (c:=13) face5rrrrrlll face5rrrrrllr
theorem face5rrrrrlrll : Good (85/54:ℚ) 7 11 ⟨46,some 93⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) (.snd 11 .leaf (.fst 61 (.fst 52 .leaf (.snd 12 .leaf (.fst 56 .leaf (.fst 58 .leaf .leaf)))) (.fst 74 (.snd 12 (.fst 67 .leaf (.fst 70 .leaf (.fst 72 .leaf .leaf))) .leaf) .leaf))) (by decide +kernel)
theorem face5rrrrrlrlr : Good (85/54:ℚ) 7 11 ⟨94,none⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) (.snd 11 (.fst 189 (.fst 125 (.snd 10 .leaf (.fst 107 (.fst 100 .leaf (.fst 103 (.fst 101 .leaf (.fst 102 .leaf .leaf)) .leaf)) .leaf)) (.snd 10 .leaf .leaf)) (.fst 381 (.snd 10 (.fst 253 (.fst 217 (.fst 202 (.fst 195 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) (by decide +kernel)
theorem face5rrrrrlrl : Good (85/54:ℚ) 7 11 ⟨46,none⟩ ⟨10,some 13⟩ := first (c:=93) face5rrrrrlrll face5rrrrrlrlr
theorem face5rrrrrlrr : Good (85/54:ℚ) 7 11 ⟨46,none⟩ ⟨14,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.fst 93 (.snd 16 (.fst 61 (.fst 52 (.snd 14 (.fst 48 .leaf (.fst 50 (.fst 49 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face5rrrrrlr : Good (85/54:ℚ) 7 11 ⟨46,none⟩ ⟨10,some 21⟩ := second (c:=13) face5rrrrrlrl face5rrrrrlrr
theorem face5rrrrrl : Good (85/54:ℚ) 7 11 ⟨22,none⟩ ⟨10,some 21⟩ := first (c:=45) face5rrrrrll face5rrrrrlr
theorem face5rrrrrrllll : Good (85/54:ℚ) 7 11 ⟨22,some 29⟩ ⟨22,some 29⟩ := sound (by norm_num) (by decide) (by decide) (.fst 25 (.snd 25 .leaf (.fst 23 .leaf (.snd 27 .leaf (.fst 24 .leaf .leaf)))) (.snd 25 (.fst 27 (.snd 23 .leaf (.fst 26 .leaf .leaf)) (.snd 23 (.fst 28 (.snd 22 .leaf .leaf) .leaf) .leaf)) .leaf)) (by decide +kernel)
theorem face5rrrrrrlllr : Good (85/54:ℚ) 7 11 ⟨22,some 29⟩ ⟨30,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.fst 25 (.snd 36 (.fst 23 (.snd 32 .leaf (.fst 22 (.snd 34 .leaf (.snd 35 .leaf .leaf)) .leaf)) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face5rrrrrrlll : Good (85/54:ℚ) 7 11 ⟨22,some 29⟩ ⟨22,some 45⟩ := second (c:=29) face5rrrrrrllll face5rrrrrrlllr
theorem face5rrrrrrllr : Good (85/54:ℚ) 7 11 ⟨30,some 45⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrrrll : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨22,some 45⟩ := first (c:=29) face5rrrrrrlll face5rrrrrrllr
theorem face5rrrrrrlr : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨46,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrrrl : Good (85/54:ℚ) 7 11 ⟨22,some 45⟩ ⟨22,none⟩ := second (c:=45) face5rrrrrrll face5rrrrrrlr
theorem face5rrrrrrr : Good (85/54:ℚ) 7 11 ⟨46,none⟩ ⟨22,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face5rrrrrr : Good (85/54:ℚ) 7 11 ⟨22,none⟩ ⟨22,none⟩ := first (c:=45) face5rrrrrrl face5rrrrrrr
theorem face5rrrrr : Good (85/54:ℚ) 7 11 ⟨22,none⟩ ⟨10,none⟩ := second (c:=21) face5rrrrrl face5rrrrrr
theorem face5rrrr : Good (85/54:ℚ) 7 11 ⟨10,none⟩ ⟨10,none⟩ := first (c:=21) face5rrrrl face5rrrrr
theorem face5rrr : Good (85/54:ℚ) 7 11 ⟨10,none⟩ ⟨4,none⟩ := second (c:=9) face5rrrl face5rrrr
theorem face5rr : Good (85/54:ℚ) 7 11 ⟨4,none⟩ ⟨4,none⟩ := first (c:=9) face5rrl face5rrr
theorem face5r : Good (85/54:ℚ) 7 11 ⟨4,none⟩ ⟨1,none⟩ := second (c:=3) face5rl face5rr
theorem face5 : Good (85/54:ℚ) 7 11 ⟨1,none⟩ ⟨1,none⟩ := first (c:=3) face5l face5r
#print axioms face5
theorem face7l : Good (119/81:ℚ) 5 11 ⟨1,some 3⟩ ⟨1,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rl : Good (119/81:ℚ) 5 11 ⟨4,some 9⟩ ⟨1,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrl : Good (119/81:ℚ) 5 11 ⟨10,none⟩ ⟨1,some 3⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrl : Good (119/81:ℚ) 5 11 ⟨10,some 21⟩ ⟨4,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrl : Good (119/81:ℚ) 5 11 ⟨22,none⟩ ⟨4,some 9⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrll : Good (119/81:ℚ) 5 11 ⟨22,some 45⟩ ⟨10,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrlrll : Good (119/81:ℚ) 5 11 ⟨22,some 29⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrlrlrl : Good (119/81:ℚ) 5 11 ⟨22,some 25⟩ ⟨46,none⟩ := sound (by norm_num) (by decide) (by decide) (.snd 93 .leaf (.fst 23 .leaf (.snd 189 .leaf (.snd 381 (.fst 24 .leaf (.snd 253 .leaf (.snd 304 .leaf (.snd 338 (.snd 320 (.snd 312 .leaf .leaf) .leaf) .leaf)))) (.fst 24 .leaf .leaf))))) (by decide +kernel)
theorem face7rrrrrlrlrrl : Good (119/81:ℚ) 5 11 ⟨26,some 29⟩ ⟨46,some 93⟩ := sound (by norm_num) (by decide) (by decide) (.snd 61 .leaf (.fst 27 .leaf (.snd 74 (.fst 28 .leaf .leaf) .leaf))) (by decide +kernel)
theorem face7rrrrrlrlrrr : Good (119/81:ℚ) 5 11 ⟨26,some 29⟩ ⟨94,none⟩ := sound (by norm_num) (by decide) (by decide) (.snd 189 (.fst 27 (.snd 125 (.fst 26 .leaf (.snd 107 (.snd 100 (.snd 96 .leaf (.snd 98 (.snd 97 .leaf .leaf) .leaf)) .leaf) .leaf)) (.fst 26 (.snd 151 (.snd 137 .leaf (.snd 144 .leaf (.snd 147 (.snd 145 .leaf (.snd 146 .leaf .leaf)) .leaf))) .leaf) .leaf)) .leaf) .leaf) (by decide +kernel)
theorem face7rrrrrlrlrr : Good (119/81:ℚ) 5 11 ⟨26,some 29⟩ ⟨46,none⟩ := second (c:=93) face7rrrrrlrlrrl face7rrrrrlrlrrr
theorem face7rrrrrlrlr : Good (119/81:ℚ) 5 11 ⟨22,some 29⟩ ⟨46,none⟩ := first (c:=25) face7rrrrrlrlrl face7rrrrrlrlrr
theorem face7rrrrrlrl : Good (119/81:ℚ) 5 11 ⟨22,some 29⟩ ⟨22,none⟩ := second (c:=45) face7rrrrrlrll face7rrrrrlrlr
theorem face7rrrrrlrrlll : Good (119/81:ℚ) 5 11 ⟨30,some 36⟩ ⟨22,some 29⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrlrrllrl : Good (119/81:ℚ) 5 11 ⟨30,some 32⟩ ⟨30,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.snd 36 .leaf (.fst 30 .leaf (.snd 40 .leaf (.fst 31 .leaf (.snd 42 (.snd 41 .leaf .leaf) .leaf))))) (by decide +kernel)
theorem face7rrrrrlrrllrr : Good (119/81:ℚ) 5 11 ⟨33,some 36⟩ ⟨30,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.snd 36 (.fst 34 (.snd 32 .leaf (.fst 33 .leaf (.snd 34 .leaf .leaf))) (.snd 32 (.fst 35 .leaf (.snd 30 .leaf .leaf)) .leaf)) (.fst 34 (.snd 40 (.fst 33 (.snd 38 (.snd 37 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (by decide +kernel)
theorem face7rrrrrlrrllr : Good (119/81:ℚ) 5 11 ⟨30,some 36⟩ ⟨30,some 45⟩ := first (c:=32) face7rrrrrlrrllrl face7rrrrrlrrllrr
theorem face7rrrrrlrrll : Good (119/81:ℚ) 5 11 ⟨30,some 36⟩ ⟨22,some 45⟩ := second (c:=29) face7rrrrrlrrlll face7rrrrrlrrllr
theorem face7rrrrrlrrlr : Good (119/81:ℚ) 5 11 ⟨37,some 45⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.snd 29 (.fst 40 (.snd 25 (.fst 38 .leaf (.snd 23 .leaf (.fst 39 .leaf (.snd 24 .leaf .leaf)))) (.fst 38 (.snd 27 .leaf (.fst 37 (.snd 28 .leaf .leaf) .leaf)) .leaf)) (.snd 25 (.fst 42 (.snd 23 .leaf .leaf) (.snd 23 (.fst 43 (.snd 22 .leaf .leaf) .leaf) .leaf)) .leaf)) .leaf) (by decide +kernel)
theorem face7rrrrrlrrl : Good (119/81:ℚ) 5 11 ⟨30,some 45⟩ ⟨22,some 45⟩ := first (c:=36) face7rrrrrlrrll face7rrrrrlrrlr
theorem face7rrrrrlrrr : Good (119/81:ℚ) 5 11 ⟨30,some 45⟩ ⟨46,none⟩ := sound (by norm_num) (by decide) (by decide) (.fst 36 (.snd 93 (.fst 32 (.snd 61 (.fst 30 (.snd 52 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face7rrrrrlrr : Good (119/81:ℚ) 5 11 ⟨30,some 45⟩ ⟨22,none⟩ := second (c:=45) face7rrrrrlrrl face7rrrrrlrrr
theorem face7rrrrrlr : Good (119/81:ℚ) 5 11 ⟨22,some 45⟩ ⟨22,none⟩ := first (c:=29) face7rrrrrlrl face7rrrrrlrr
theorem face7rrrrrl : Good (119/81:ℚ) 5 11 ⟨22,some 45⟩ ⟨10,none⟩ := second (c:=21) face7rrrrrll face7rrrrrlr
theorem face7rrrrrrlll : Good (119/81:ℚ) 5 11 ⟨46,some 93⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) (.fst 61 .leaf (.snd 11 .leaf (.fst 74 .leaf (.fst 83 .leaf (.snd 12 .leaf (.fst 88 .leaf .leaf)))))) (by decide +kernel)
theorem face7rrrrrrllrll : Good (119/81:ℚ) 5 11 ⟨46,some 61⟩ ⟨14,some 16⟩ := sound (by norm_num) (by decide) (by decide) (.fst 52 .leaf (.snd 14 .leaf (.fst 56 .leaf (.snd 15 .leaf (.fst 58 .leaf (.fst 59 .leaf (.fst 60 .leaf .leaf))))))) (by decide +kernel)
theorem face7rrrrrrllrlr : Good (119/81:ℚ) 5 11 ⟨46,some 61⟩ ⟨17,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.fst 52 (.snd 18 .leaf (.fst 48 (.snd 19 .leaf (.fst 46 (.snd 20 .leaf .leaf) (.snd 20 (.fst 47 .leaf .leaf) .leaf))) (.snd 19 (.fst 50 (.fst 49 .leaf .leaf) .leaf) .leaf))) (.snd 18 (.fst 56 (.snd 17 (.fst 54 .leaf (.fst 55 .leaf .leaf)) .leaf) .leaf) .leaf)) (by decide +kernel)
theorem face7rrrrrrllrl : Good (119/81:ℚ) 5 11 ⟨46,some 61⟩ ⟨14,some 21⟩ := second (c:=16) face7rrrrrrllrll face7rrrrrrllrlr
theorem face7rrrrrrllrr : Good (119/81:ℚ) 5 11 ⟨62,some 93⟩ ⟨14,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.snd 16 (.fst 74 (.snd 14 .leaf (.fst 67 (.snd 15 (.fst 64 .leaf (.fst 65 .leaf (.fst 66 .leaf .leaf))) .leaf) .leaf)) (.snd 14 (.fst 83 (.fst 78 (.fst 76 (.fst 75 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) (by decide +kernel)
theorem face7rrrrrrllr : Good (119/81:ℚ) 5 11 ⟨46,some 93⟩ ⟨14,some 21⟩ := first (c:=61) face7rrrrrrllrl face7rrrrrrllrr
theorem face7rrrrrrll : Good (119/81:ℚ) 5 11 ⟨46,some 93⟩ ⟨10,some 21⟩ := second (c:=13) face7rrrrrrlll face7rrrrrrllr
theorem face7rrrrrrlrll : Good (119/81:ℚ) 5 11 ⟨94,some 189⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) (.snd 11 (.fst 125 .leaf (.snd 10 .leaf (.fst 151 .leaf (.fst 168 (.fst 159 (.fst 155 (.fst 153 .leaf (.fst 154 .leaf .leaf)) .leaf) .leaf) .leaf)))) (.fst 125 (.fst 107 (.snd 12 .leaf .leaf) (.snd 12 (.fst 115 (.fst 111 (.fst 109 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)) (by decide +kernel)
theorem face7rrrrrrlrlr : Good (119/81:ℚ) 5 11 ⟨190,none⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) (.snd 11 (.fst 381 (.snd 10 (.fst 253 .leaf (.fst 304 (.fst 276 .leaf (.fst 289 .leaf (.fst 296 (.fst 292 .leaf (.fst 294 (.fst 293 .leaf .leaf) .leaf)) .leaf))) .leaf)) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face7rrrrrrlrl : Good (119/81:ℚ) 5 11 ⟨94,none⟩ ⟨10,some 13⟩ := first (c:=189) face7rrrrrrlrll face7rrrrrrlrlr
theorem face7rrrrrrlrr : Good (119/81:ℚ) 5 11 ⟨94,none⟩ ⟨14,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrrlr : Good (119/81:ℚ) 5 11 ⟨94,none⟩ ⟨10,some 21⟩ := second (c:=13) face7rrrrrrlrl face7rrrrrrlrr
theorem face7rrrrrrl : Good (119/81:ℚ) 5 11 ⟨46,none⟩ ⟨10,some 21⟩ := first (c:=93) face7rrrrrrll face7rrrrrrlr
theorem face7rrrrrrr : Good (119/81:ℚ) 5 11 ⟨46,none⟩ ⟨22,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face7rrrrrr : Good (119/81:ℚ) 5 11 ⟨46,none⟩ ⟨10,none⟩ := second (c:=21) face7rrrrrrl face7rrrrrrr
theorem face7rrrrr : Good (119/81:ℚ) 5 11 ⟨22,none⟩ ⟨10,none⟩ := first (c:=45) face7rrrrrl face7rrrrrr
theorem face7rrrr : Good (119/81:ℚ) 5 11 ⟨22,none⟩ ⟨4,none⟩ := second (c:=9) face7rrrrl face7rrrrr
theorem face7rrr : Good (119/81:ℚ) 5 11 ⟨10,none⟩ ⟨4,none⟩ := first (c:=21) face7rrrl face7rrrr
theorem face7rr : Good (119/81:ℚ) 5 11 ⟨10,none⟩ ⟨1,none⟩ := second (c:=3) face7rrl face7rrr
theorem face7r : Good (119/81:ℚ) 5 11 ⟨4,none⟩ ⟨1,none⟩ := first (c:=9) face7rl face7rr
theorem face7 : Good (119/81:ℚ) 5 11 ⟨1,none⟩ ⟨1,none⟩ := first (c:=3) face7l face7r
#print axioms face7
theorem face11l : Good (187/135:ℚ) 5 7 ⟨1,some 3⟩ ⟨1,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rl : Good (187/135:ℚ) 5 7 ⟨4,none⟩ ⟨1,some 3⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrl : Good (187/135:ℚ) 5 7 ⟨4,some 9⟩ ⟨4,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrl : Good (187/135:ℚ) 5 7 ⟨10,none⟩ ⟨4,some 9⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrl : Good (187/135:ℚ) 5 7 ⟨10,some 21⟩ ⟨10,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrll : Good (187/135:ℚ) 5 7 ⟨22,some 45⟩ ⟨10,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrl : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨10,some 13⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrrl : Good (187/135:ℚ) 5 7 ⟨46,some 93⟩ ⟨14,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrrrll : Good (187/135:ℚ) 5 7 ⟨94,some 189⟩ ⟨14,some 16⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrrrlr : Good (187/135:ℚ) 5 7 ⟨190,none⟩ ⟨14,some 16⟩ := sound (by norm_num) (by decide) (by decide) (.fst 381 .leaf (.snd 14 .leaf (.fst 765 .leaf (.snd 15 .leaf (.fst 1533 .leaf (.fst 3069 (.fst 2045 (.fst 1753 .leaf (.fst 1888 .leaf (.fst 1963 (.fst 1925 .leaf (.fst 1944 (.fst 1934 .leaf (.fst 1939 .leaf (.fst 1941 .leaf (.fst 1942 .leaf (.fst 1943 .leaf .leaf))))) .leaf)) .leaf))) .leaf) .leaf)))))) (by decide +kernel)
theorem face11rrrrrlrrrl : Good (187/135:ℚ) 5 7 ⟨94,none⟩ ⟨14,some 16⟩ := first (c:=189) face11rrrrrlrrrll face11rrrrrlrrrlr
theorem face11rrrrrlrrrrll : Good (187/135:ℚ) 5 7 ⟨94,some 189⟩ ⟨17,some 18⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrrrrlrl : Good (187/135:ℚ) 5 7 ⟨94,some 125⟩ ⟨19,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.snd 19 .leaf (.fst 107 (.snd 20 .leaf (.fst 100 .leaf (.fst 103 .leaf (.fst 105 (.fst 104 .leaf .leaf) .leaf)))) (.snd 20 (.fst 115 .leaf (.fst 120 .leaf (.fst 122 .leaf (.fst 123 .leaf .leaf)))) .leaf))) (by decide +kernel)
theorem face11rrrrrlrrrrlrr : Good (187/135:ℚ) 5 7 ⟨126,some 189⟩ ⟨19,some 21⟩ := sound (by norm_num) (by decide) (by decide) (.snd 19 (.fst 151 .leaf (.fst 168 (.fst 159 (.fst 155 (.fst 153 .leaf (.fst 154 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf) (by decide +kernel)
theorem face11rrrrrlrrrrlr : Good (187/135:ℚ) 5 7 ⟨94,some 189⟩ ⟨19,some 21⟩ := first (c:=125) face11rrrrrlrrrrlrl face11rrrrrlrrrrlrr
theorem face11rrrrrlrrrrl : Good (187/135:ℚ) 5 7 ⟨94,some 189⟩ ⟨17,some 21⟩ := second (c:=18) face11rrrrrlrrrrll face11rrrrrlrrrrlr
theorem face11rrrrrlrrrrrl : Good (187/135:ℚ) 5 7 ⟨190,none⟩ ⟨17,some 18⟩ := sound (by norm_num) (by decide) (by decide) (.fst 381 (.fst 253 (.snd 17 .leaf (.fst 217 (.fst 202 .leaf (.fst 209 .leaf (.fst 213 (.fst 211 .leaf (.fst 212 .leaf .leaf)) .leaf))) .leaf)) (.snd 17 (.fst 304 .leaf (.fst 338 .leaf (.fst 358 .leaf (.fst 369 (.fst 363 .leaf (.fst 366 .leaf (.fst 367 .leaf .leaf))) .leaf)))) .leaf)) .leaf) (by decide +kernel)
theorem face11rrrrrlrrrrrr : Good (187/135:ℚ) 5 7 ⟨190,none⟩ ⟨19,some 21⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrlrrrrr : Good (187/135:ℚ) 5 7 ⟨190,none⟩ ⟨17,some 21⟩ := second (c:=18) face11rrrrrlrrrrrl face11rrrrrlrrrrrr
theorem face11rrrrrlrrrr : Good (187/135:ℚ) 5 7 ⟨94,none⟩ ⟨17,some 21⟩ := first (c:=189) face11rrrrrlrrrrl face11rrrrrlrrrrr
theorem face11rrrrrlrrr : Good (187/135:ℚ) 5 7 ⟨94,none⟩ ⟨14,some 21⟩ := second (c:=16) face11rrrrrlrrrl face11rrrrrlrrrr
theorem face11rrrrrlrr : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨14,some 21⟩ := first (c:=93) face11rrrrrlrrl face11rrrrrlrrr
theorem face11rrrrrlr : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨10,some 21⟩ := second (c:=13) face11rrrrrlrl face11rrrrrlrr
theorem face11rrrrrl : Good (187/135:ℚ) 5 7 ⟨22,none⟩ ⟨10,some 21⟩ := first (c:=45) face11rrrrrll face11rrrrrlr
theorem face11rrrrrrlll : Good (187/135:ℚ) 5 7 ⟨22,some 29⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrllrl : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨22,some 29⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrllrrl : Good (187/135:ℚ) 5 7 ⟨30,some 36⟩ ⟨30,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrllrrrl : Good (187/135:ℚ) 5 7 ⟨37,some 45⟩ ⟨30,some 36⟩ := sound (by norm_num) (by decide) (by decide) (.fst 40 .leaf (.snd 32 .leaf (.fst 42 .leaf (.snd 34 .leaf (.fst 43 .leaf (.fst 44 .leaf (.snd 35 .leaf .leaf))))))) (by decide +kernel)
theorem face11rrrrrrllrrrr : Good (187/135:ℚ) 5 7 ⟨37,some 45⟩ ⟨37,some 45⟩ := sound (by norm_num) (by decide) (by decide) (.fst 40 (.snd 40 .leaf (.fst 38 .leaf (.snd 42 .leaf (.snd 43 (.fst 39 .leaf .leaf) .leaf)))) (.snd 40 (.fst 42 (.snd 38 .leaf (.fst 41 .leaf (.snd 39 .leaf .leaf))) (.snd 38 (.fst 43 (.snd 37 .leaf .leaf) .leaf) .leaf)) .leaf)) (by decide +kernel)
theorem face11rrrrrrllrrr : Good (187/135:ℚ) 5 7 ⟨37,some 45⟩ ⟨30,some 45⟩ := second (c:=36) face11rrrrrrllrrrl face11rrrrrrllrrrr
theorem face11rrrrrrllrr : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨30,some 45⟩ := first (c:=36) face11rrrrrrllrrl face11rrrrrrllrrr
theorem face11rrrrrrllr : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨22,some 45⟩ := second (c:=29) face11rrrrrrllrl face11rrrrrrllrr
theorem face11rrrrrrll : Good (187/135:ℚ) 5 7 ⟨22,some 45⟩ ⟨22,some 45⟩ := first (c:=29) face11rrrrrrlll face11rrrrrrllr
theorem face11rrrrrrlrll : Good (187/135:ℚ) 5 7 ⟨22,some 29⟩ ⟨46,some 93⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrlrlrl : Good (187/135:ℚ) 5 7 ⟨22,some 25⟩ ⟨94,none⟩ := sound (by norm_num) (by decide) (by decide) (.snd 189 .leaf (.fst 23 .leaf (.snd 381 .leaf (.snd 765 (.fst 24 .leaf (.snd 509 .leaf (.snd 612 (.snd 556 (.snd 532 (.snd 520 .leaf (.snd 526 (.snd 523 (.snd 521 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))) (.fst 24 .leaf .leaf))))) (by decide +kernel)
theorem face11rrrrrrlrlrrl : Good (187/135:ℚ) 5 7 ⟨26,some 29⟩ ⟨94,some 189⟩ := sound (by norm_num) (by decide) (by decide) (.fst 27 (.snd 125 .leaf (.snd 151 .leaf (.fst 26 .leaf (.snd 168 (.snd 159 .leaf (.snd 163 .leaf .leaf)) .leaf)))) (.snd 125 (.snd 107 (.fst 28 .leaf (.snd 100 .leaf (.snd 103 (.snd 101 .leaf (.snd 102 .leaf .leaf)) .leaf))) (.fst 28 .leaf .leaf)) .leaf)) (by decide +kernel)
theorem face11rrrrrrlrlrrr : Good (187/135:ℚ) 5 7 ⟨26,some 29⟩ ⟨190,none⟩ := sound (by norm_num) (by decide) (by decide) (.fst 27 (.snd 381 (.snd 253 (.fst 26 (.snd 217 .leaf (.snd 234 .leaf (.snd 243 .leaf (.snd 248 (.snd 245 (.snd 244 .leaf .leaf) .leaf) .leaf)))) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face11rrrrrrlrlrr : Good (187/135:ℚ) 5 7 ⟨26,some 29⟩ ⟨94,none⟩ := second (c:=189) face11rrrrrrlrlrrl face11rrrrrrlrlrrr
theorem face11rrrrrrlrlr : Good (187/135:ℚ) 5 7 ⟨22,some 29⟩ ⟨94,none⟩ := first (c:=25) face11rrrrrrlrlrl face11rrrrrrlrlrr
theorem face11rrrrrrlrl : Good (187/135:ℚ) 5 7 ⟨22,some 29⟩ ⟨46,none⟩ := second (c:=93) face11rrrrrrlrll face11rrrrrrlrlr
theorem face11rrrrrrlrrlll : Good (187/135:ℚ) 5 7 ⟨30,some 36⟩ ⟨46,some 61⟩ := sound (by norm_num) (by decide) (by decide) (.fst 32 .leaf (.snd 52 (.fst 34 .leaf (.snd 48 .leaf (.fst 35 .leaf (.snd 50 .leaf (.snd 51 .leaf .leaf))))) (.fst 34 (.snd 56 .leaf (.fst 33 .leaf (.snd 58 .leaf .leaf))) (.snd 56 (.fst 35 (.snd 54 .leaf .leaf) .leaf) .leaf)))) (by decide +kernel)
theorem face11rrrrrrlrrllrll : Good (187/135:ℚ) 5 7 ⟨30,some 32⟩ ⟨62,some 74⟩ := sound (by norm_num) (by decide) (by decide) (.fst 30 .leaf (.snd 67 .leaf (.fst 31 .leaf (.snd 70 (.snd 68 .leaf (.snd 69 .leaf .leaf)) .leaf)))) (by decide +kernel)
theorem face11rrrrrrlrrllrlr : Good (187/135:ℚ) 5 7 ⟨30,some 32⟩ ⟨75,some 93⟩ := sound (by norm_num) (by decide) (by decide) (.fst 30 (.snd 83 .leaf (.snd 88 (.snd 85 .leaf (.snd 86 .leaf (.snd 87 .leaf .leaf))) .leaf)) (.snd 83 (.fst 31 (.snd 78 (.snd 76 .leaf (.snd 77 .leaf .leaf)) .leaf) .leaf) .leaf)) (by decide +kernel)
theorem face11rrrrrrlrrllrl : Good (187/135:ℚ) 5 7 ⟨30,some 32⟩ ⟨62,some 93⟩ := second (c:=74) face11rrrrrrlrrllrll face11rrrrrrlrrllrlr
theorem face11rrrrrrlrrllrr : Good (187/135:ℚ) 5 7 ⟨33,some 36⟩ ⟨62,some 93⟩ := sound (by norm_num) (by decide) (by decide) (.snd 74 (.fst 34 (.snd 67 (.fst 33 (.snd 64 (.snd 62 .leaf (.snd 63 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face11rrrrrrlrrllr : Good (187/135:ℚ) 5 7 ⟨30,some 36⟩ ⟨62,some 93⟩ := first (c:=32) face11rrrrrrlrrllrl face11rrrrrrlrrllrr
theorem face11rrrrrrlrrll : Good (187/135:ℚ) 5 7 ⟨30,some 36⟩ ⟨46,some 93⟩ := second (c:=61) face11rrrrrrlrrlll face11rrrrrrlrrllr
theorem face11rrrrrrlrrlr : Good (187/135:ℚ) 5 7 ⟨37,some 45⟩ ⟨46,some 93⟩ := sound (by norm_num) (by decide) (by decide) (.snd 61 (.fst 40 (.snd 52 (.fst 38 (.snd 48 (.fst 37 .leaf (.snd 46 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face11rrrrrrlrrl : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨46,some 93⟩ := first (c:=36) face11rrrrrrlrrll face11rrrrrrlrrlr
theorem face11rrrrrrlrrr : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨94,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrlrr : Good (187/135:ℚ) 5 7 ⟨30,some 45⟩ ⟨46,none⟩ := second (c:=93) face11rrrrrrlrrl face11rrrrrrlrrr
theorem face11rrrrrrlr : Good (187/135:ℚ) 5 7 ⟨22,some 45⟩ ⟨46,none⟩ := first (c:=29) face11rrrrrrlrl face11rrrrrrlrr
theorem face11rrrrrrl : Good (187/135:ℚ) 5 7 ⟨22,some 45⟩ ⟨22,none⟩ := second (c:=45) face11rrrrrrll face11rrrrrrlr
theorem face11rrrrrrrllll : Good (187/135:ℚ) 5 7 ⟨46,some 61⟩ ⟨22,some 29⟩ := sound (by norm_num) (by decide) (by decide) (.snd 25 .leaf (.fst 52 .leaf (.fst 56 (.snd 27 .leaf (.fst 54 .leaf (.snd 28 .leaf (.fst 55 .leaf .leaf)))) (.snd 27 .leaf (.fst 58 (.snd 28 .leaf .leaf) .leaf))))) (by decide +kernel)
theorem face11rrrrrrrlllrll : Good (187/135:ℚ) 5 7 ⟨62,some 74⟩ ⟨22,some 25⟩ := sound (by norm_num) (by decide) (by decide) (.snd 23 .leaf (.fst 67 .leaf (.fst 70 (.snd 24 .leaf (.fst 68 .leaf (.fst 69 .leaf .leaf))) (.snd 24 .leaf .leaf)))) (by decide +kernel)
theorem face11rrrrrrrlllrlr : Good (187/135:ℚ) 5 7 ⟨75,some 93⟩ ⟨22,some 25⟩ := sound (by norm_num) (by decide) (by decide) (.snd 23 (.fst 83 (.fst 78 .leaf (.snd 22 .leaf (.fst 80 .leaf (.fst 81 .leaf (.fst 82 .leaf .leaf))))) (.snd 22 (.fst 88 .leaf (.fst 90 .leaf (.fst 91 .leaf .leaf))) .leaf)) (.fst 83 (.fst 78 (.snd 24 (.fst 76 (.fst 75 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (by decide +kernel)
theorem face11rrrrrrrlllrl : Good (187/135:ℚ) 5 7 ⟨62,some 93⟩ ⟨22,some 25⟩ := first (c:=74) face11rrrrrrrlllrll face11rrrrrrrlllrlr
theorem face11rrrrrrrlllrr : Good (187/135:ℚ) 5 7 ⟨62,some 93⟩ ⟨26,some 29⟩ := sound (by norm_num) (by decide) (by decide) (.fst 74 (.fst 67 (.snd 27 (.fst 64 (.snd 26 .leaf .leaf) (.snd 26 (.fst 65 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face11rrrrrrrlllr : Good (187/135:ℚ) 5 7 ⟨62,some 93⟩ ⟨22,some 29⟩ := second (c:=25) face11rrrrrrrlllrl face11rrrrrrrlllrr
theorem face11rrrrrrrlll : Good (187/135:ℚ) 5 7 ⟨46,some 93⟩ ⟨22,some 29⟩ := first (c:=61) face11rrrrrrrllll face11rrrrrrrlllr
theorem face11rrrrrrrllrlll : Good (187/135:ℚ) 5 7 ⟨46,some 52⟩ ⟨30,some 36⟩ := sound (by norm_num) (by decide) (by decide) (.snd 32 (.fst 48 .leaf (.snd 30 .leaf (.fst 50 (.snd 31 .leaf (.fst 49 .leaf .leaf)) (.snd 31 (.fst 51 .leaf .leaf) .leaf)))) (.fst 48 (.snd 34 (.fst 46 .leaf (.snd 33 .leaf (.fst 47 .leaf .leaf))) .leaf) .leaf)) (by decide +kernel)
theorem face11rrrrrrrllrllr : Good (187/135:ℚ) 5 7 ⟨53,some 61⟩ ⟨30,some 36⟩ := sound (by norm_num) (by decide) (by decide) (.snd 32 (.fst 56 (.snd 30 (.fst 54 (.fst 53 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) (by decide +kernel)
theorem face11rrrrrrrllrll : Good (187/135:ℚ) 5 7 ⟨46,some 61⟩ ⟨30,some 36⟩ := first (c:=52) face11rrrrrrrllrlll face11rrrrrrrllrllr
theorem face11rrrrrrrllrlr : Good (187/135:ℚ) 5 7 ⟨46,some 61⟩ ⟨37,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrrllrl : Good (187/135:ℚ) 5 7 ⟨46,some 61⟩ ⟨30,some 45⟩ := second (c:=36) face11rrrrrrrllrll face11rrrrrrrllrlr
theorem face11rrrrrrrllrr : Good (187/135:ℚ) 5 7 ⟨62,some 93⟩ ⟨30,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrrllr : Good (187/135:ℚ) 5 7 ⟨46,some 93⟩ ⟨30,some 45⟩ := first (c:=61) face11rrrrrrrllrl face11rrrrrrrllrr
theorem face11rrrrrrrll : Good (187/135:ℚ) 5 7 ⟨46,some 93⟩ ⟨22,some 45⟩ := second (c:=29) face11rrrrrrrlll face11rrrrrrrllr
theorem face11rrrrrrrlr : Good (187/135:ℚ) 5 7 ⟨94,none⟩ ⟨22,some 45⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrrl : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨22,some 45⟩ := first (c:=93) face11rrrrrrrll face11rrrrrrrlr
theorem face11rrrrrrrr : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨46,none⟩ := sound (by norm_num) (by decide) (by decide) .leaf (by decide +kernel)
theorem face11rrrrrrr : Good (187/135:ℚ) 5 7 ⟨46,none⟩ ⟨22,none⟩ := second (c:=45) face11rrrrrrrl face11rrrrrrrr
theorem face11rrrrrr : Good (187/135:ℚ) 5 7 ⟨22,none⟩ ⟨22,none⟩ := first (c:=45) face11rrrrrrl face11rrrrrrr
theorem face11rrrrr : Good (187/135:ℚ) 5 7 ⟨22,none⟩ ⟨10,none⟩ := second (c:=21) face11rrrrrl face11rrrrrr
theorem face11rrrr : Good (187/135:ℚ) 5 7 ⟨10,none⟩ ⟨10,none⟩ := first (c:=21) face11rrrrl face11rrrrr
theorem face11rrr : Good (187/135:ℚ) 5 7 ⟨10,none⟩ ⟨4,none⟩ := second (c:=9) face11rrrl face11rrrr
theorem face11rr : Good (187/135:ℚ) 5 7 ⟨4,none⟩ ⟨4,none⟩ := first (c:=9) face11rrl face11rrr
theorem face11r : Good (187/135:ℚ) 5 7 ⟨4,none⟩ ⟨1,none⟩ := second (c:=3) face11rl face11rr
theorem face11 : Good (187/135:ℚ) 5 7 ⟨1,none⟩ ⟨1,none⟩ := first (c:=3) face11l face11r
#print axioms face11
end OMA.FiveFace245212
