(*****************************************************************************
 * Future word-cell authentication entry point.                              *
 *                                                                            *
 * Keep the completed authentication library frozen so its existing theory   *
 * clients do not rebuild.  New chunks call this wrapper: it performs the     *
 * established authentication once, then immediately saves clock-parametric   *
 * entry theorems from those new saved facts.                                 *
 *****************************************************************************)
structure compute_boundedCase16594WordChunkClockLib = struct

open HolKernel;

fun authenticate_cells
      {data_theory:string,cell_indices:int list,chunk_prefix:string} =
  let
    val authentication =
      compute_boundedCase16594WordChunkLib.authenticate_cells
        {data_theory=data_theory,
         cell_indices=cell_indices,
         chunk_prefix=chunk_prefix};
    val clock_entries =
      compute_boundedCase16594WordClockRetrofitLib.retrofit_cells
        {auth_theory=current_theory (),
         cell_indices=cell_indices,
         chunk_prefix=chunk_prefix};
  in
    {authentication=authentication,
     clock_entries=clock_entries}
  end;

end
