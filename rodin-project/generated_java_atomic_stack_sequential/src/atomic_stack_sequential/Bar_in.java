package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Bar_in{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Bar_in(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (new Enumerated(new Integer(1),machine.nbFloors).has(destinationFloor) && !machine.get_workingElement().equals(machine.null) && ((destinationFloor.equals(new Integer(6))) ==> (!machine.get_barFrom().equals(new Integer(0)))) && machine.get_barTo().equals(new Integer(0)) && !machine.get_stack().apply(destinationFloor).restrictRangeTo(new BSet<Integer>(machine.null)).equals(BSet.EMPTY) && destinationFloor.equals(machine.get_elementLift()) && !machine.get_elementOnLift().equals(machine.null)); */
	public /*@ pure */ boolean guard_Bar_in( Integer destinationFloor) {
		return (new Enumerated(new Integer(1),machine.nbFloors).has(destinationFloor) && !machine.get_workingElement().equals(machine.null) && BOOL.implication(destinationFloor.equals(new Integer(6)),!machine.get_barFrom().equals(new Integer(0))) && machine.get_barTo().equals(new Integer(0)) && !machine.get_stack().apply(destinationFloor).restrictRangeTo(new BSet<Integer>(machine.null)).equals(BSet.EMPTY) && destinationFloor.equals(machine.get_elementLift()) && !machine.get_elementOnLift().equals(machine.null));
	}

	/*@ public normal_behavior
		requires guard_Bar_in(destinationFloor);
		assignable machine.barTo;
		ensures guard_Bar_in(destinationFloor) &&  machine.get_barTo() == \old(destinationFloor); 
	 also
		requires !guard_Bar_in(destinationFloor);
		assignable \nothing;
		ensures true; */
	public void run_Bar_in( Integer destinationFloor){
		if(guard_Bar_in(destinationFloor)) {
			Integer barTo_tmp = machine.get_barTo();

			machine.set_barTo(destinationFloor);

			System.out.println("Bar_in executed destinationFloor: " + destinationFloor + " ");
		}
	}

}
