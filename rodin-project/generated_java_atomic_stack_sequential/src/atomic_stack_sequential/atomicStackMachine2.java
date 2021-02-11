package atomic_stack_sequential;

import eventb_prelude.*;
import Util.*;
//@ model import org.jmlspecs.models.JMLObjectSet;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class atomicStackMachine2{
	private static final Integer max_integer = Utilities.max_integer;
	private static final Integer min_integer = Utilities.min_integer;

	Bar_new evt_Bar_new = new Bar_new(this);
	BeltOut_roll evt_BeltOut_roll = new BeltOut_roll(this);
	Bar_withdraw evt_Bar_withdraw = new Bar_withdraw(this);
	Lift_down evt_Lift_down = new Lift_down(this);
	Lift_up evt_Lift_up = new Lift_up(this);
	Bar_out evt_Bar_out = new Bar_out(this);
	Bar_insert evt_Bar_insert = new Bar_insert(this);
	Send_out evt_Send_out = new Send_out(this);
	Bar_in evt_Bar_in = new Bar_in(this);
	BeltIn_roll evt_BeltIn_roll = new BeltIn_roll(this);


	/******Set definitions******/
	//@ public static constraint ELEMENTS.equals(\old(ELEMENTS)); 
	public static final BSet<Integer> ELEMENTS = new Enumerated(min_integer,max_integer);


	/******Constant definitions******/
	//@ public static constraint nbElementsPerFloor.equals(\old(nbElementsPerFloor)); 
	public static final Integer nbElementsPerFloor = Test_atomicStackMachine2.random_nbElementsPerFloor;

	//@ public static constraint nbFloors.equals(\old(nbFloors)); 
	public static final Integer nbFloors = Test_atomicStackMachine2.random_nbFloors;

	//@ public static constraint cadmium.equals(\old(cadmium)); 
	public static final Integer cadmium = Test_atomicStackMachine2.random_cadmium;

	//@ public static constraint null.equals(\old(null)); 
	public static final Integer null = Test_atomicStackMachine2.random_null;

	//@ public static constraint uranium.equals(\old(uranium)); 
	public static final Integer uranium = Test_atomicStackMachine2.random_uranium;



	/******Axiom definitions******/
	/*@ public static invariant nbFloors.equals(new Integer(6)); */
	/*@ public static invariant nbElementsPerFloor.equals(new Integer(2)); */
	/*@ public static invariant BSet.partition(ELEMENTS,new BSet<Integer>(cadmium),new BSet<Integer>(uranium),new BSet<Integer>(null)); */


	/******Variable definitions******/
	/*@ spec_public */ private Integer barFrom;

	/*@ spec_public */ private Integer barTo;

	/*@ spec_public */ private BRelation<Integer,Integer> beltIn;

	/*@ spec_public */ private BRelation<Integer,Integer> beltOut;

	/*@ spec_public */ private Integer elementLift;

	/*@ spec_public */ private Integer elementOnLift;

	/*@ spec_public */ private Boolean handlingElement;

	/*@ spec_public */ private BRelation<Integer,Integer> simpleStack;

	/*@ spec_public */ private BRelation<Integer,BRelation<Integer,Integer>> stack;

	/*@ spec_public */ private Integer workingElement;




	/******Invariant definition******/
	/*@ public invariant
		new Enumerated(new Integer(0),nbFloors).has(barTo) &&
		new Enumerated(new Integer(0),nbFloors).has(barFrom) &&
		BOOL.instance.has(handlingElement) &&
		 simpleStack.domain().equals(new Enumerated(new Integer(1),nbFloors)) && simpleStack.range().isSubset(new Enumerated(new Integer(0),nbElementsPerFloor)) && simpleStack.isaFunction() && BRelation.cross(new Enumerated(new Integer(1),nbFloors),new Enumerated(new Integer(0),nbElementsPerFloor)).has(simpleStack) &&
		!(barTo.equals(nbFloors) && barFrom.equals(new Integer(0))) &&
		barTo.equals(new Integer(0)) || (simpleStack.apply(barTo)).compareTo(nbElementsPerFloor) < 0 &&
		new Enumerated(new Integer(0),nbFloors).has(barTo) &&
		new Enumerated(new Integer(0),nbFloors).has(barFrom) &&
		 stack.domain().equals(new Enumerated(new Integer(1),nbFloors)) && stack.range().isSubset(BRelation.cross(new Enumerated(new Integer(1),nbElementsPerFloor),ELEMENTS)) && stack.isaFunction() && BRelation.cross(new Enumerated(new Integer(1),nbFloors),BRelation.cross(new Enumerated(new Integer(1),nbElementsPerFloor),ELEMENTS)).has(stack) &&
		ELEMENTS.has(workingElement) &&
		((!workingElement.equals(null)) <==> (handlingElement.equals(true))) &&
		 (\forall Integer floor;((stack.domain().has(floor)) ==> (simpleStack.apply(floor).equals(new Integer(stack.apply(floor).rangeSubtraction(new BSet<Integer>(null)).size()))))) &&
		 (\forall Integer floor;((stack.domain().has(floor)) ==> ( (\forall Integer elem;((stack.apply(floor).domain().difference(new BSet<Integer>(nbElementsPerFloor)).has(elem)) ==> (((!stack.apply(floor).apply(elem).equals(null)) ==> (!stack.apply(floor).apply(new Integer(elem + new Integer(1))).equals(null))))))))) &&
		new Enumerated(new Integer(0),nbFloors).has(elementLift) &&
		 beltIn.domain().equals(new BSet<Integer>(new Integer(1),new Integer(2))) && beltIn.range().isSubset(ELEMENTS) && beltIn.isaFunction() && BRelation.cross(new BSet<Integer>(new Integer(1),new Integer(2)),ELEMENTS).has(beltIn) &&
		 beltOut.domain().equals(new BSet<Integer>(new Integer(1),new Integer(2))) && beltOut.range().isSubset(ELEMENTS) && beltOut.isaFunction() && BRelation.cross(new BSet<Integer>(new Integer(1),new Integer(2)),ELEMENTS).has(beltOut) &&
		ELEMENTS.has(elementOnLift); */


	/******Getter and Mutator methods definition******/
	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.elementLift;*/
	public /*@ pure */ Integer get_elementLift(){
		return this.elementLift;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.elementLift;
	    ensures this.elementLift == elementLift;*/
	public void set_elementLift(Integer elementLift){
		this.elementLift = elementLift;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.handlingElement;*/
	public /*@ pure */ Boolean get_handlingElement(){
		return this.handlingElement;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.handlingElement;
	    ensures this.handlingElement == handlingElement;*/
	public void set_handlingElement(Boolean handlingElement){
		this.handlingElement = handlingElement;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.simpleStack;*/
	public /*@ pure */ BRelation<Integer,Integer> get_simpleStack(){
		return this.simpleStack;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.simpleStack;
	    ensures this.simpleStack == simpleStack;*/
	public void set_simpleStack(BRelation<Integer,Integer> simpleStack){
		this.simpleStack = simpleStack;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.stack;*/
	public /*@ pure */ BRelation<Integer,BRelation<Integer,Integer>> get_stack(){
		return this.stack;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.stack;
	    ensures this.stack == stack;*/
	public void set_stack(BRelation<Integer,BRelation<Integer,Integer>> stack){
		this.stack = stack;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.beltOut;*/
	public /*@ pure */ BRelation<Integer,Integer> get_beltOut(){
		return this.beltOut;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.beltOut;
	    ensures this.beltOut == beltOut;*/
	public void set_beltOut(BRelation<Integer,Integer> beltOut){
		this.beltOut = beltOut;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.barTo;*/
	public /*@ pure */ Integer get_barTo(){
		return this.barTo;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.barTo;
	    ensures this.barTo == barTo;*/
	public void set_barTo(Integer barTo){
		this.barTo = barTo;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.barFrom;*/
	public /*@ pure */ Integer get_barFrom(){
		return this.barFrom;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.barFrom;
	    ensures this.barFrom == barFrom;*/
	public void set_barFrom(Integer barFrom){
		this.barFrom = barFrom;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.beltIn;*/
	public /*@ pure */ BRelation<Integer,Integer> get_beltIn(){
		return this.beltIn;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.beltIn;
	    ensures this.beltIn == beltIn;*/
	public void set_beltIn(BRelation<Integer,Integer> beltIn){
		this.beltIn = beltIn;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.workingElement;*/
	public /*@ pure */ Integer get_workingElement(){
		return this.workingElement;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.workingElement;
	    ensures this.workingElement == workingElement;*/
	public void set_workingElement(Integer workingElement){
		this.workingElement = workingElement;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.elementOnLift;*/
	public /*@ pure */ Integer get_elementOnLift(){
		return this.elementOnLift;
	}

	/*@ public normal_behavior
	    requires true;
	    assignable this.elementOnLift;
	    ensures this.elementOnLift == elementOnLift;*/
	public void set_elementOnLift(Integer elementOnLift){
		this.elementOnLift = elementOnLift;
	}



	/*@ public normal_behavior
	    requires true;
	    assignable \everything;
	    ensures
		barTo == 0 &&
		barFrom == 0 &&
		workingElement == null &&
		stack == BRelation.cross(new Enumerated(1,nbFloors),new BSet<Integer>(BRelation.cross(new Enumerated(1,nbElementsPerFloor),new BSet<Integer>(null)))) &&
		elementLift == 0 &&
		beltIn.equals(BRelation.cross(new BSet<Integer>(1,2),new BSet<Integer>(null))) &&
		beltOut.equals(BRelation.cross(new BSet<Integer>(1,2),new BSet<Integer>(null))) &&
		elementOnLift == null;*/
	public atomicStackMachine2(){
		barTo = 0;
		barFrom = 0;
		workingElement = null;
		stack = BRelation.cross(new Enumerated(1,nbFloors),new BSet<Integer>(BRelation.cross(new Enumerated(1,nbElementsPerFloor),new BSet<Integer>(null))));
		elementLift = 0;
		beltIn = (BRelation.cross(new BSet<Integer>(1,2),new BSet<Integer>(null)));
		beltOut = (BRelation.cross(new BSet<Integer>(1,2),new BSet<Integer>(null)));
		elementOnLift = null;

	}
}