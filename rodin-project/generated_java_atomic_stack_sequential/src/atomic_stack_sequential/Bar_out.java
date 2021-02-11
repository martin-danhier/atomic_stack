package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Bar_out{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Bar_out(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (machine.get_barTo().equals(new Integer(0)) && !machine.get_workingElement().equals(machine.null) && !machine.get_beltOut().apply(new Integer(2)).equals(machine.null)); */
	public /*@ pure */ boolean guard_Bar_out() {
		return (machine.get_barTo().equals(new Integer(0)) && !machine.get_workingElement().equals(machine.null) && !machine.get_beltOut().apply(new Integer(2)).equals(machine.null));
	}

	/*@ public normal_behavior
		requires guard_Bar_out();
		assignable machine.barFrom, machine.workingElement, machine.beltOut;
		ensures guard_Bar_out() &&  machine.get_barFrom() == \old(0) &&  machine.get_workingElement() == \old(machine.null) &&  machine.get_beltOut().equals(\old((machine.get_beltOut().override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(2,machine.null)))))); 
	 also
		requires !guard_Bar_out();
		assignable \nothing;
		ensures true; */
	public void run_Bar_out(){
		if(guard_Bar_out()) {
			Integer barFrom_tmp = machine.get_barFrom();
			Integer workingElement_tmp = machine.get_workingElement();
			BRelation<Integer,Integer> beltOut_tmp = machine.get_beltOut();

			machine.set_barFrom(0);
			machine.set_workingElement(machine.null);
			machine.set_beltOut((beltOut_tmp.override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(2,machine.null)))));

			System.out.println("Bar_out executed ");
		}
	}

}
