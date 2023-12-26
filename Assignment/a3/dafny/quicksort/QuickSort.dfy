include "part.dfy"


method qsort(a:array<int>, l:nat, u:nat)
  requires a.Length > 0;
  requires l <= u < a.Length;
  requires l <= u < a.Length;
  requires l>0 ==> partitioned(a, 0, l-1, l, u);
  requires u+1 <= a.Length -1 ==> partitioned(a, l, u, u+1, a.Length-1);
  modifies a;
  ensures sorted_between(a, l, u+1);
  ensures l > 0 ==> beq(old(a[..]), a[..], 0, l-1);
  ensures l > 0 ==> partitioned(a, 0, l-1, l, u);
  ensures u < a.Length-1 ==> beq(old(a[..]), a[..], u+1, a.Length - 1);
  ensures u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);
  ensures u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);
  decreases u - l


  // complete the code for quicksort and verify the implementation
  {
  if (l < u) { 
    var pivot := partition(a, l, u);
    assert forall i :: l <= i < pivot ==> a[i] <= a[pivot];
    assert forall i :: pivot < i < u ==> a[pivot] <= a[i];
    if (pivot > l) {
      qsort(a, l, pivot-1); // Recursive call on the left part only if pivot is greater than l
      assert sorted_between(a, l, pivot); 
    }
    if (pivot < u) {
      // Recursive call on the right part only if pivot is less than u
      qsort(a, pivot + 1, u);
    }
  }
}
