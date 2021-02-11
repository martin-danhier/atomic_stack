package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Bar_withdraw{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Bar_withdraw(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (new Enumerated(new Integer(1),machine.nbFloors).has(fromFloor) && !machine.get_stack().apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).equals(BSet.EMPTY) && machine.get_barFrom().equals(new Integer(0)) && machine.get_workingElement().equals(machine.null) && machine.get_elementLift().equals(fromFloor)); */
	public /*@ pure */ boolean guard_Bar_withdraw( Integer fromFloor) {
		return (new Enumerated(new Integer(1),machine.nbFloors).has(fromFloor) && !machine.get_stack().apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).equals(BSet.EMPTY) && machine.get_barFrom().equals(new Integer(0)) && machine.get_workingElement().equals(machine.null) && machine.get_elementLift().equals(fromFloor));
	}

	/*@ public normal_behavior
		requires guard_Bar_withdraw(fromFloor);
		assignable machine.workingElement, machine.barFrom, machine.stack, machine.elementOnLift;
		ensures guard_Bar_withdraw(fromFloor) &&  machine.get_workingElement() == \old(machine.get_stack().apply(fromFloor).apply(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(machine.get_stack().apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1))) &&  machine.get_barFrom() == \old(fromFloor) &&  machine.get_stack().equals(\old((machine.get_stack().override(new BRelation<Integer,BRelation<Integer,Integer>>(new Pair<Integer,BRelation<Integer,Integer>>(fromFloor,(machine.get_stack().apply(fromFloor).override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(machine.get_stack().apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1),machine.null)))))))))) &&  machine.get_elementOnLift() == \old(machine.get_stack().apply(fromFloor).apply(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(machine.get_stack().apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1))); 
	 also
		requires !guard_Bar_withdraw(fromFloor);
		assignable \nothing;
		ensures true; */
	public void run_Bar_withdraw( Integer fromFloor){
		if(guard_Bar_withdraw(fromFloor)) {
			Integer workingElement_tmp = machine.get_workingElement();
			Integer barFrom_tmp = machine.get_barFrom();
			BRelation<Integer,BRelation<Integer,Integer>> stack_tmp = machine.get_stack();
			Integer elementOnLift_tmp = machine.get_elementOnLift();

			machine.set_workingElement(stack_tmp.apply(fromFloor).apply(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(stack_tmp.apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1)));
			machine.set_barFrom(fromFloor);
			machine.set_stack((stack_tmp.override(new BRelation<Integer,BRelation<Integer,Integer>>(new Pair<Integer,BRelation<Integer,Integer>>(fromFloor,(stack_tmp.apply(fromFloor).override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(stack_tmp.apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1),machine.null)))))))));
			machine.set_elementOnLift(stack_tmp.apply(fromFloor).apply(new Integer(new Integer(machine.nbElementsPerFloor - new Integer(stack_tmp.apply(fromFloor).rangeSubtraction(new BSet<Integer>(machine.null)).size())) + 1)));

			System.out.println("Bar_withdraw executed fromFloor: " + fromFloor + " ");
		}
	}

}
