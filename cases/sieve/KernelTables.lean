import CheckedMediumOrders

namespace WildSieve

private theorem orders : checkedMediumOrders.map CheckedOrder.order=(List.range 36).map (fun i => 83+2*i) := by decide

theorem medium_certificate (n : Nat) (lo : 83≤n) (hi : n≤153) (odd : n%2=1) :
    ∃ h,Cert n (fixedSize n) (levels n) h := by
  have member : n∈checkedMediumOrders.map CheckedOrder.order := by
    rw [orders]
    exact List.mem_map.mpr ⟨(n-83)/2,List.mem_range.mpr (by omega),by omega⟩
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp member
  exact ⟨_,cert_of_table k.order _ _ k.table k.passed⟩

#print axioms medium_certificate
end WildSieve
