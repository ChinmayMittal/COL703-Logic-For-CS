%% Run this program Using
%% swipl -s solution.pl -g "main." -t halt

main :-
    % Order of Boxes is[RED | PINK | WHITE | BLACK | GREEN]
    Boxes = [[_, _], [_, _], [_, _], [_, _], [_, _]],  % Structure for five boxes
    Balls = [r, r, p, p, w, w, b, b, g, g],            % All available balls
    
    % Apply constraints
    valid_arrangement(Boxes, Balls),
    !,  % Cut to prevent backtracking after finding a solution
    print_boxes(Boxes),
    nl.


%%%%%%%%% PRINT HELPER %%%%%%%%%%%%%
print_boxes([]). % Base Case
print_boxes([[A, B]|Boxes]) :-
    write(A), write(B), % Print the Ball
    print_boxes(Boxes). % Move on the next Ball
%%%%%%%%% PRINT HELPER %%%%%%%%%%%%%



valid_arrangement(Boxes, Balls) :-
    % Assign balls to boxes based on constraints
    assign_balls(Boxes, Balls),
    
    % Check each constraint
    no_ball_matches_box_color(Boxes), % condition (a)
    no_pink_in_red(Boxes), % constraint (b)
    neutral_box_red_green(Boxes), % constraint (c)
    black_box_cold_colors(Boxes), % constraint (d)
    box_white_pink(Boxes), % constraint (e)
    black_ball_in_pink_box(Boxes). % constraint (f)


%%%%%%%%%%%% Ball assignment %%%%%%%%%%%%%%
assign_balls(_, []).
assign_balls(Boxes, [Ball|Balls]) :-
    select_box(Boxes, Ball),
    assign_balls(Boxes, Balls).

select_box([[A, B]|_], Ball) :-
    var(A), A = Ball; %% ensure that the spot is not already full using Var(A)
    var(B), B = Ball.
select_box([_|Boxes], Ball) :- %% skip box
    select_box(Boxes, Ball).

%%%%%%%%%%%% Ball assignment %%%%%%%%%%%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicate to ensure no ball matches the color of its box
% Constraint (a)
no_ball_matches_box_color(Boxes) :-
    no_red_in_red_box(Boxes),
    no_pink_in_pink_box(Boxes),
    no_white_in_white_box(Boxes),
    no_black_in_black_box(Boxes),
    no_green_in_green_box(Boxes).


no_red_in_red_box(Boxes) :-
    Boxes = [[Ball1, Ball2]|_],
    Ball1 \= r,
    Ball2 \= r.

no_pink_in_pink_box(Boxes) :-
    Boxes = [_, [Ball1, Ball2]|_],
    Ball1 \= p,
    Ball2 \= p.

no_white_in_white_box(Boxes) :-
    Boxes = [_, _, [Ball1, Ball2]|_],
    Ball1 \= w,
    Ball2 \= w.

no_black_in_black_box(Boxes) :-
    Boxes = [_, _, _, [Ball1, Ball2]|_],
    Ball1 \= b,
    Ball2 \= b.

no_green_in_green_box(Boxes) :-
    Boxes = [_, _, _, _, [Ball1, Ball2]],
    Ball1 \= g,
    Ball2 \= g.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Constraint (b)
no_pink_in_red(Boxes) :-
    Boxes = [[Ball1, Ball2]|_],  % Extract the first list (red box) from Boxes
    Ball1 \= p,  % Ensure the first ball is not pink
    Ball2 \= p.  % Ensure the second ball is not pink

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Constraint (c)
neutral_box_red_green(Boxes) :-
    black_box_red_green(Boxes);           % Check if the black box has a red and green ball
    white_box_red_green(Boxes).           % Or check if the white box has a red and green ball

black_box_red_green(Boxes) :-
    Boxes = [_, _, _, [Ball1, Ball2]|_],  % Extract the fourth list (black box) from Boxes
    member(r, [Ball1, Ball2]),            % Ensure one of the balls is red
    member(g, [Ball1, Ball2]).            % Ensure one of the balls is green


white_box_red_green(Boxes) :-
    Boxes = [_, _, [Ball1, Ball2]|_],     % Extract the third list (white box) from Boxes
    member(r, [Ball1, Ball2]),            % Ensure one of the balls is red
    member(g, [Ball1, Ball2]).            % Ensure one of the balls is green

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Constraint (d)
% Predicate to ensure the black box contains atleast one green or pink ball (cold colors)
black_box_cold_colors(Boxes) :-
    Boxes = [_, _, _, [Ball1, Ball2]|_],  % Extract the fourth list (black box) from Boxes
    member(Ball1, [g, p]);               % Ensure the first ball is either green or pink
    member(Ball2, [g, p]).               % Ensure the second ball is either green or pink

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Constraint (e)

box_white_pink(Boxes) :- % there is atleast a box with a white and pink ball inside
    red_box_white_pink(Boxes);
    pink_box_white_pink(Boxes);
    white_box_white_pink(Boxes);
    black_box_white_pink(Boxes);
    green_box_white_pink(Boxes).


red_box_white_pink(Boxes) :-
    Boxes = [[Ball1, Ball2]|_],
    member(w, [Ball1, Ball2]),
    member(p, [Ball1, Ball2]).

pink_box_white_pink(Boxes) :-
    Boxes = [_, [Ball1, Ball2]|_],
    member(w, [Ball1, Ball2]),
    member(p, [Ball1, Ball2]).


white_box_white_pink(Boxes) :-
    Boxes = [_, _, [Ball1, Ball2]|_],
    member(w, [Ball1, Ball2]),
    member(p, [Ball1, Ball2]).

black_box_white_pink(Boxes) :-
    Boxes = [_, _, _, [Ball1, Ball2]|_],
    member(w, [Ball1, Ball2]),
    member(p, [Ball1, Ball2]).

green_box_white_pink(Boxes) :-
    Boxes = [_, _, _, _, [Ball1, Ball2]],
    member(w, [Ball1, Ball2]),
    member(p, [Ball1, Ball2]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicate to ensure there is a black ball in the pink box
%% Constraint (f)
black_ball_in_pink_box(Boxes) :-
    Boxes = [_, [Ball1, Ball2]|_],  % Extract the second list (pink box) from Boxes
    (Ball1 = b; Ball2 = b).         % Ensure at least one of the balls is black
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%