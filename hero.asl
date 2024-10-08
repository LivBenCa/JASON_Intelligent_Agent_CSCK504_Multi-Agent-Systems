//STUDENT NAME: Benedikt Geitz
//STUDENT ID: 200051442

/*Beliefs & rules*/
//Hero is at the position of agent P (variable),
//if agent P's position is identical to Hero's position.
at(P) :- pos(P,X,Y) & pos(hero,X,Y).

/*Initial goals*/
!started. //The initial goal is the first goal the agent has and needs
		//to start with a plan.

/*Plans*/
//The following plans usually start with a +!goal that is used when the goal
//becomes a new intention for the agent. -!goals are good to throw errors or
//to show when intentions have been dropped.

//The +!started goal was given and leads via !check(slots) to the next plan.
+!started : true
   <- .print("I'm not scared of that smelly Goblin!");
   		!check(slots).

//!check(slots) is the main goal to move the agent through the grid. It checks
//if the agent collected already all three needed items for the goblin. If not,
//it asks for the position of the hero and saves the coordinates in the
//variables PX,PY. Then performs the given next(slot) action. Afterwards it asks
//again for the agent's position and stores the new coordinates in the variables
//LX,LY. In the end, it passes over to the next goal.
+!check(slots) : not hero(gem) | not hero(coin) | not hero(vase)
	<- ?pos(hero,PX,PY);
		next(slot);
		?pos(hero, LX, LY);
		!check_teleport(LX,LY,PX,PY).

//If the hero collected all three needed items, the !at(goblin) goal is started.
+!check(slots) : hero(gem) & hero(coin) & hero(vase)
	<- !at(goblin).

//If the check(slots) goal is no longer the intention of the hero (which means
//in this case, the hero cannot proceed through the grid), an error message is
//generated to the logger.
-!check(slots)
	<- .print("Failed to check slots.").

//The +!check_teleport(LX,LY,PX,PY) goal detects unsual movement that does not
//match the next(slot) action and indicates the usage of a teleporter. Therefore
//it compares the two variables PY,LY. If the difference is 3, the teleporter
//has been used and the move_to goal is triggered. Before it does that, it
//informs the logger about the detection.
+!check_teleport(LX,LY,PX,PY): LY == PY+3
	<- .print("Teleporter Detection");
		!move_to(teleporter).

//If the difference of LY,PY is not 3 there is no teleportation detected and
//the agent can proceed with its way through the grid. Therefore it checks its
//position with the !check(position) goal.
+!check_teleport(LX,LY,PX,PY): not LY == PY+3
	<-!check(position).

//The move_to(teleporter) plan checks if the hero is at position 2,5 which is in
//front of the missing gem and processes to the !check(slots) to pick it up.
+!move_to(teleporter) : pos(hero, 2,5)
	<- !check(slots).

//If the hero is not on the position 2,5 it moves towards this position. This
//plan is recursive to since the move_forward action only steps one slot forward
+!move_to(teleporter) : not pos(hero,2,5)
	<- move_towards(2,5);
		!move_to(teleporter).

//The !check(position) goal/plan checks if the hero reached the end of the grid
//which is position(7,7). If the position is reached, the logger is informed and
//!check(treasure) goal is triggered.
+!check(position) : pos(hero,7,7)
	<- .print("End of grid reached!");
			!check(treasure).
//If the position has not been reached by he hero yet, the hero starts looking
//for an object at the current position with the !find(object) goal.
+!check(position) : not pos(hero,7,7)
	<- !find(object).

//In case the hero reached the end of the grid and did not find all three items,
//the logger is informed about it.
+!check(treasure) : not hero(gem) | not hero(coin) | not hero(vase)
	<- .print("I cannot find all objects!").

//The !find(object) plan looks if there is an object (gem, coin or vase) on the
//position of the hero. If it is, the !detect(object) goal is triggered.
+!find(object) : gem(hero) | coin(hero) | vase(hero)
	<- !detect(object).

//If there is no such object, the hero moves on to the next slot.
+!find(object) : not gem(hero) | not coin(hero) | not vase(hero)
	<- !check(slots).

//The !detect(object) goal/plan detects the type of the object. Once it knows
//if it is a gem, coin or vase, it checks if the hero already carries this item.
//if the hero does not carry it, the !take(object, hero) plan is triggered.
+!detect(object) : gem(hero) & not hero(gem)
	<- .print("Gem!");
		!take(object, hero).

+!detect(object) : vase(hero) & not hero(vase)
	<- .print("Vase!");
		!take(object, hero).

+!detect(object) : coin(hero) & not hero(coin)
	<- .print("Coin!");
		!take(object, hero).

//In case the hero carries the object already, the logger is informed and the
//hero moves on.
+!detect(object) : coin(hero) & hero(coin)
		<- .print("I carry this object already.")
		!check(slots).

+!detect(object) : vase(hero) & hero(vase)
		<- .print("I carry this object already.")
		!check(slots).

+!detect(object) : gem(hero) & hero(gem)
		<- .print("I carry this object already.")
		!check(slots).

//The !take(object, hero) goal/plan handles the pick() action for all possible
//objects at the same time and after a successful pick() passes on to the
//!check(slots) goal/plan.
+!take(object, hero) : true
	<- !ensure_pick(object);
		!check(slots).

//The !ensure_pick(object) takes care of the coincidence when the pick()action
//is unsuccessful and acts recursive as long as one of the three given objects
//is at the position of the hero. It picks either one of them by trying to pick
//all of them.
+!ensure_pick(object) : gem(hero)|vase(hero)|coin(hero)
	<- pick(coin);
		pick(vase);
		pick(gem);
		!ensure_pick(object).

//Once the pick()action is successful and no more object available, the logger
//is informed about the success.
+!ensure_pick(object) : not gem(hero)|not vase(hero)|not coin(hero)
	<- .print("Pick successful").

//The !at(goblin) goal/plan checks if the hero is the position of the goblin.
//It further checks if the goblin still needs the certain object, and if the
//hero carries the object. If all conditions are fulfilled, the object is
//dropped and the goblin stashes the item. This plan is recursive and all items
//are checked.
+!at(goblin) : at(goblin) & not goblin(gem) & hero(gem)
	<- drop(gem);
	stash(gem);
		!at(goblin).

+!at(goblin) : at(goblin) & not goblin(vase) & hero(vase)
	<- drop(vase);
	stash(vase);
		!at(goblin).

+!at(goblin) : at(goblin) & not goblin(coin) & hero(coin)
	<- drop(coin);
	stash(coin);
		!at(goblin).

//Once the hero carries no more items, the logger is informed, that the goblin
//is satisfied and the task is finished.
+!at(goblin) : at(goblin) & not hero(coin) & not hero(vase) & not hero(gem)
	<- .print("Goblin satisfied!").

//In case the hero is not at the position of the goblin, the hero will ask for
//the position of the goblin and move then towards it. Since the move_towards()
//action only steps one slot at a time, the plan is recursive until the hero
//reached the goblin's position.
+!at(goblin) : not at(goblin)
	<- ?pos(goblin, X, Y);
		move_towards(X,Y);
			!at(goblin).

