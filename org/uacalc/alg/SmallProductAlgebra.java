package org.uacalc.alg;

import java.util.*;
import org.uacalc.util.*;

public class SmallProductAlgebra extends BigProductAlgebra implements SmallAlgebra {
	private List<IntArray> universeList = null;
	private Map<IntArray,Integer> universeOrder = null;
	
	public SmallProductAlgebra(SmallAlgebra alg, int power) {
		super(alg,power);
	}
	
	@Override
	public AlgebraType algebraType() {
		return SmallAlgebra.AlgebraType.PRODUCT;
	}

	@Override
	public Object getElement(int k) {
		return new IntArray(Horner.hornerInv(k, sizes));
	}

	@Override
	public int elementIndex(Object elem) {
		if ( elem instanceof IntArray ) {
			return Horner.horner(((IntArray)elem).toArray(), sizes);
		} // end if ( elem instanceof IntArray )
		return -1;
	}

	@Override
	public List getUniverseList() {
		if (universeList!=null) return universeList;
		universeList = new ArrayList<IntArray>();
		for ( int i = 0; i < super.cardinality(); i++ ) universeList.add(new IntArray(Horner.hornerInv(i, sizes)));
		return universeList;
	}

	@Override
	public Map getUniverseOrder() {
		if (universeOrder!=null) return universeOrder;
		universeOrder = new HashMap<IntArray, Integer>();
		for ( int i = 0; i < super.cardinality(); i++ ) universeOrder.put(new IntArray(Horner.hornerInv(i, sizes)), new Integer(i));
		return universeOrder;
	}

	@Override
	public void convertToDefaultValueOps() {}

}
