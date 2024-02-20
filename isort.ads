with Sort_Types; use Sort_Types;

package ISort with SPARK_Mode is
   
   -- A is sorted in range I .. J.
   -- Returns true if I >= J
   function Sorted(A : in Nat_Array; I : Positive; J : Natural) 
		  return Boolean
   is
      (for all K in I .. J - 1 => A(K) <= A(K+1))
   with 
	Ghost,
	Pre => I in A'First .. A'Last + 1 and then 
	       J in A'First - 1 .. A'Last;


   -- Sort the elements in the array A into ascending order
   procedure Insertion_Sort (A : in out Nat_Array)
     with
     Pre => A'Length > 0,
     Post => Sorted(A, A'First, A'Last);
   
end ISort;
