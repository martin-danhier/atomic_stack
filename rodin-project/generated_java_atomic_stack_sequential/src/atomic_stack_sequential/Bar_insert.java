package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Bar_insert{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Bar_insert(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (!machine.get_barTo().equals(new Integer(0)) && !machine.get_workingElement().equals(machine.null) && machine.get_elementLift().equals(machine.get_barTo())); */
	public /*@ pure */ boolean guard_Bar_insert() {
		return (!machine.get_barTo().equals(new Integer(0)) && !machine.get_workingElement().equals(machine.null) && machine.get_elementLift().equals(machine.get_barTo()));
	}

	/*@ public normal_behavior
		requires guard_Bar_insert();
		assignable machine.stack, machine.barTo, machine.barFrom, machine.workingElement, machine.elementOnLift;
		ensures guard_Bar_insert() &&  machine.get_stack().equals(\old((machine.get_stack().override(new BRelation<Integer,BRelation<Integer,Integer>>(new Pair<Integer,BRelation<Integer,Integer>>(machine.get_barTo(),(machine.get_stack().apply(machine.get_barTo()).override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(new Integer(machine.nbElementsPerFloor - new Integer(machine.get_stack().apply(machine.get_barTo()).rangeSubtraction(new BSet<Integer>(machine.null)).size())),machine.get_workingElement())))))))))) &&  machine.get_barTo() == \old(0) &&  machine.get_barFrom() == \old(0) &&  machine.get_workingElement() == \old(machine.null) &&  machine.get_elementOnLift() == \old(machine.null); 
	 also
		requires !guard_Bar_insert();
		assignable \nothing;
		ensures true; */
	public void run_Bar_insert(){
		if(guard_Bar_insert()) {
			BRelation<Integer,BRelation<Integer,Integer>> stack_tmp = machine.get_stack();
			Integer barTo_tmp = machine.get_barTo();
			Integer barFrom_tmp = machine.get_barFrom();
			Integer workingElement_tmp = machine.get_workingElement();
			Integer elementOnLift_tmp = machine.get_elementOnLift();

			machine.set_stack((stack_tmp.override(new BRelation<Integer,BRelation<Integer,Integer>>(new Pair<Integer,BRelation<Integer,Integer>>(barTo_tmp,(stack_tmp.apply(barTo_tmp).override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(new Integer(machine.nbElementsPerFloor - new Integer(stack_tmp.apply(barTo_tmp).rangeSubtraction(new BSet<Integer>(machine.null)).size())),workingElement_tmp)))))))));
			machine.set_barTo(0);
			machine.set_barFrom(0);
			machine.set_workingElement(machine.null);
			machine.set_elementOnLift(machine.null);

			System.out.println("Bar_insert executed ");
		}
	}

}
