package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Bar_new{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Bar_new(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (machine.get_barTo().equals(new Integer(0)) && machine.get_barFrom().equals(new Integer(0)) && machine.ELEMENTS.difference(new BSet<Integer>(machine.null)).has(element) && machine.get_workingElement().equals(machine.null) && machine.get_stack().apply(machine.nbFloors).rangeSubtraction(new BSet<Integer>(machine.null)).equals(BSet.EMPTY)); */
	public /*@ pure */ boolean guard_Bar_new( Integer element) {
		return (machine.get_barTo().equals(new Integer(0)) && machine.get_barFrom().equals(new Integer(0)) && machine.ELEMENTS.difference(new BSet<Integer>(machine.null)).has(element) && machine.get_workingElement().equals(machine.null) && machine.get_stack().apply(machine.nbFloors).rangeSubtraction(new BSet<Integer>(machine.null)).equals(BSet.EMPTY));
	}

	/*@ public normal_behavior
		requires guard_Bar_new(element);
		assignable machine.workingElement, machine.beltIn;
		ensures guard_Bar_new(element) &&  machine.get_workingElement() == \old(element) &&  machine.get_beltIn().equals(\old((machine.get_beltIn().override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,element)))))); 
	 also
		requires !guard_Bar_new(element);
		assignable \nothing;
		ensures true; */
	public void run_Bar_new( Integer element){
		if(guard_Bar_new(element)) {
			Integer workingElement_tmp = machine.get_workingElement();
			BRelation<Integer,Integer> beltIn_tmp = machine.get_beltIn();

			machine.set_workingElement(element);
			machine.set_beltIn((beltIn_tmp.override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,element)))));

			System.out.println("Bar_new executed element: " + element + " ");
		}
	}

}
