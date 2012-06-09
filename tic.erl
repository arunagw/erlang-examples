% --------------------------------------------------------------
% tic.erl
% --------------------------------------------------------------
%
%   Tic tac toe game written in Erlang.
%
%   tic:play( ) to play the game.
%   Reads/writes standard IO.
%   Character (not graphics) user-interface.

-module( tic ).
-author( "Neal Binnendyk" ).
-copyright( "Copyright (c) 2009 Neal Binnendyk, Ixacta Inc" ).
-export([ play/0 ]).

% --------------------------------------------------------------
% Utility Macros - m_assert(..) and m_confirm(..)
% --------------------------------------------------------------
% ?m_assert( Pred )
% ?m_confirm( Confirm_fn, Expr )
%
%   Simple assert and confirm macros.
%
%   m_assert alerts the user and halts the program if Pred is
%   any value other than 'true'. With debugging off Pred is not
%   evaluated.
%
%   m_confirm( Confirm_fn, Expr ) returns (Expr), but before
%   returning it asserts that Confirm_fn( Expr) evaluates
%   true.
%
%   If you want something a little more comprehensive try:
%     http://erlang.org/download/eunit.hrl

-ifdef( NODEBUG ).

- define( m_assert( Pred ), ok ).
- define( m_confirm( Confirm_fn, Expr ), (Expr) ).

-else.

- define(
m_assert( Pred ),
  ( (fun ( Pred_evaled ) ->
       case Pred_evaled of
         true -> ok;
         _ ->
           io:fwrite( "~nAssert failed in ~w at line ~w~n",
             [ ?MODULE, ?LINE ]),
           io:fwrite( "Expression is "),
           io:fwrite( ??Pred),
           io:fwrite( "~n  which evaluates to ~w~n~n",
             [ Pred_evaled ]),
           erlang:error( assertion_failed)
       end
     end
    )( Pred)
  )).

- define(
m_confirm( Confirm_fn, Expr ),
  ( (fun ( Expr_evaled ) ->
       Confirm_evaled = Confirm_fn( Expr_evaled),
       case Confirm_evaled of
         true -> ok;
         _ ->
           io:fwrite( "~nConfirm failed in ~w at line ~w~n",
             [ ?MODULE, ?LINE ]),
           io:fwrite( "Expression is "),
           io:fwrite( ??Expr),
           io:fwrite( "~n  which evaluates to ~w~n",
             [ Expr_evaled ]),
           io:fwrite( "~nConfirm function is "),
           io:fwrite( ??Confirm_fn),
           io:fwrite( "~n  which returned ~w~n~n",
             [ Confirm_evaled ]),
           erlang:error( confirm_failed)
       end,
       Expr_evaled
     end
    )( Expr)
  )).

-endif.

% --------------------------------------------------------------
% Export Function - play()
% --------------------------------------------------------------
% play( )
%
%   Plays a game of tic-tac-toe, printing the board and reading
%   user instructions to/from standard IO.
%
%   This could print some final statistics.

play( ) ->

  % We use random:uniform(N) to break ties.
  % Take this out (or replace it with something that sets the
  % seed) if you want exact reproducability.
  randomize_random_seed( ),

  % The opening message.
  write_line( ),
  write_line( "Welcome to tic-tac-toe, the game that predicts"),
  write_line( "the outcomes of every move and lets you erase"),
  write_line( "X's and O's and skip turns."),

  % Play until the user quits.
  play_new_game( init_game( )),

  % The closing message.
  write_line( ),
  write_line( "Thanks for playing!"),
  write_line( ),
  ok.

% --------------------------------------------------------------
% play_new_game( Game )
%
%   Plays a new game created by the caller.

play_new_game( Game ) ->
  write_line( ),
  write_line( "Starting a new game."),
  case catch game_loop( Game) of
    quit -> ok;
    {new_game, Game_final} ->
      play_new_game( init_game( Game_final))
  end.

% --------------------------------------------------------------
% game_loop( Game )
%
%   Displays the board, gets user input, changes the board,
%   and calls itself tail-recursivly with the changed board.

game_loop( Game ) ->
  print_board( Game),
  game_loop(
    case get_next_move( Game) of
      quit     -> throw( quit);
      new_game -> throw( {new_game, Game});

      Option when
          Option == simple;
          Option == number;
          Option == predict ->
        set_game_print_option( Game, Option);

      skip ->
        skip_game_next_turn( Game);
      automatic ->
        automatic_game_next_turn( Game);
      {mark, Pos} ->
        mark_game_next_turn( Game, Pos);
      {erase, Pos} ->
        erase_game_next_turn( Game, Pos)
    end).

% --------------------------------------------------------------
% skip_game_next_turn( Game )
%
%   Called when the user asks to skip a turn.
%   Never called on a cat game or a game that is already won.
%
%   Returns a new #game{} object where the state is flipped
%   between "it is X's turn" and "it is O's turn".
%   May also calculate new predicted outcomes for the board.

skip_game_next_turn( Game ) ->
  set_game_state_board(
    Game,
    case get_game_state( Game) of
      x_next -> o_next;
      o_next -> x_next
    end,
    get_game_board( Game)).

% --------------------------------------------------------------
% automatic_game_next_turn( Game )
%
%   Called when the user asks the computer to choose the
%   next move.
%
%   Returns a #game{} with the new move recorded.

automatic_game_next_turn( Game ) ->
  mark_game_next_turn( Game,
    get_board_best_predicted_position(
      get_game_board( Game))).

% --------------------------------------------------------------
% mark_game_next_turn( Game, Position )
%
%   Called when the user selects a board position to mark
%   for the next move.
%
%   Returns a re-calculated #game{}.

mark_game_next_turn( Game, Pos ) ->
  State_old = get_game_state( Game),
  Board_old = clear_board_predicted_outcomes(
                get_game_board( Game)),
  ?m_assert( (State_old == x_next) or (State_old == o_next)),
  ?m_assert( get_board_mark( Board_old, Pos) == empty),

  { Xo, State_win, State_flip } =
    case State_old of
      x_next -> { x_mark, x_winner, o_next };
      o_next -> { o_mark, o_winner, x_next }
    end,

  Board_marked = mark_board( Board_old, Pos, Xo),
  set_game_state_board(
    Game,
    case is_board_won( Board_marked, Xo) of
      true  -> State_win;
      false ->
        case is_board_full( Board_marked) of
          true  -> cat_game;
          false -> State_flip
        end
    end,
    Board_marked).

% --------------------------------------------------------------
% erase_game_next_turn( Game, Position )
%
%   Erases the X or O mark on the board at position.
%
%   Returns a re-calculated #game{}.

erase_game_next_turn( Game, Pos ) ->
  State_old = get_game_state( Game),
  Board_old = clear_board_predicted_outcomes(
                get_game_board( Game)),
  Xo_old    = get_board_mark( Board_old, Pos),
  ?m_assert( (Xo_old == x_mark) or (Xo_old == o_mark)),

  Board_erased = mark_board( Board_old, Pos, empty),
  set_game_state_board(
    Game,
    case {State_old, Xo_old} of
      {cat_game, x_mark} -> x_next;
      {cat_game, o_mark} -> o_next;
      {x_winner, o_mark} -> x_winner;
      {o_winner, x_mark} -> o_winner;
      {x_next  , x_mark} -> x_next;
      {o_next  , x_mark} -> x_next;
      {x_next  , o_mark} -> o_next;
      {o_next  , o_mark} -> o_next;
      {x_winner, x_mark} ->
        case is_board_won( Board_erased, x_mark) of
          true  -> x_winner;
          false -> x_next
        end;
      {o_winner, o_mark} ->
        case is_board_won( Board_erased, o_mark) of
          true  -> o_winner;
          false -> o_next
        end
    end,
    Board_erased).

% --------------------------------------------------------------
% Record Type - #game
% --------------------------------------------------------------
%
%   The #game{} record type holds the following values:
%
%     ----------------------------------------------------------
%     state - state of the game
%       One of these atoms:
%         x_next    - it's X's turn to play next
%         o_next    - it's O's turn to play
%         x_winner  - X is the winner of the game
%         o_winner  - O is the winner
%         cat_game  - the board is full with no winner
%
%     ----------------------------------------------------------
%     board - 3x3 tic-tac-toe board
%       Tuple of 9 elements (3 rows times 3 columns).
%       See the Board section below for details.
%
%     ----------------------------------------------------------
%     print_option - how to print board
%       One of these atoms:
%         simple  - just show X's and O's
%         number  - print number in empty spots
%         predict - print number and prediction in empty slots
%
%   Suggestions:
%     Record the move history to enable undo.
%     Allow a bigger board instead of just a 3x3.
%     Record the name(s) of the players.

-record(
  game,
  {  state
   , board
   , print_option
  }).

% --------------------------------------------------------------
% Game Functions
% --------------------------------------------------------------

% --------------------------------------------------------------
% get_game_state( Game )
% get_game_board( Game )
% get_game_print_option( Game )
%
%   Simple accessors.

% One way to get a value out of the #game object.
get_game_state( _ = #game{ state=State } ) -> State.
get_game_board( _ = #game{ board=Board } ) -> Board.

% Another way to get a value out of #game.
get_game_print_option( G = #game{} ) -> G#game.print_option.

% --------------------------------------------------------------
% init_game( )
% init_game( Game = #game{} )
% init_game( Print_option )
%
%   Use this to start a game. You can carry over 

init_game( ) ->
  init_game( predict).

init_game( _ = #game{ print_option=Option } ) ->
  init_game( Option);

init_game( Print_option ) ->
  ?m_assert(
    (Print_option == simple) or
    (Print_option == number) or
    (Print_option == predict)),
  #game
   {  state        = x_next
    , board        = init_board( )
    , print_option = Print_option
   }.

% --------------------------------------------------------------
% set_game_print_option( Game, Print_option )
%
%   Returns a copy of Game with a new print option.

set_game_print_option( Game = #game{}, Option ) ->
  ?m_assert(
    (Option == simple) or
    (Option == number) or
    (Option == predict)),
  Game#game{ print_option = Option }.

% --------------------------------------------------------------
% set_game_state_board( Game, State, Board )
%
%   Returns a copy of Game with a new state and board.
%   Confirms that State and Board are consistent with each
%   other. Does not confirm that the new board is one move
%   different from the old board.

set_game_state_board( Game = #game{}, State, Board ) ->
  % State must be legal.
  ?m_assert(
    (State == x_next  ) or
    (State == o_next  ) or
    (State == x_winner) or
    (State == o_winner) or
    (State == cat_game)),

  % Winning states must agree with the board.
  % There can only be one winner.
  ?m_assert(
    (State == x_winner) == is_board_won( Board, x_mark)),
  ?m_assert(
    (State == o_winner) == is_board_won( Board, o_mark)),

  % State cat_game implies the board is full.
  ?m_assert(
    (State /= cat_game) or is_board_full( Board)),

  % Playable game implies the board is not full.
  % Remember:
  %   (A implies B) is the same as ((not A) or B)
  ?m_assert(
    ((State /= x_next) and (State /= o_next)) or
    not is_board_full( Board)),

  % If appropriate, fill the board with predicted outcomes.
  % This will fill the board with predictions even if the
  % board is empty (all spaces will predict cat games).
  % Maybe we should change that to just fill an empty board
  % with 'empty' elements.
  Board_with_predictions =
    case State of
      x_next -> fix_board_predicted_outcomes( Board, x_mark);
      o_next -> fix_board_predicted_outcomes( Board, o_mark);
      _      -> Board
    end,

  % Make a new game record.
  Game#game
   {  state = State
    , board = Board_with_predictions
   }.

% --------------------------------------------------------------
% Board Tuple and Functions
% --------------------------------------------------------------
%
%   A Board is a 9-tuple, representing a 3x3 tic-tac-toe board.
%   (9 elements is 3 rows times 3 columns.)
%
%   To examine all positions match against:
%     {_1, _2, _3, _4, _5, _6, _7, _8, _9}
%   Which correspondings to this tic-tac-toe layout:
%             |    |
%          _1 | _2 | _3
%        ----------------
%          _4 | _5 | _6
%        ----------------
%          _7 | _8 | _9
%             |    |
%
%   Each element has one of these values:
%     x_mark      - spot marked X
%     o_mark      - spot marked O
%     empty       - spot not marked
%
%   When an element is empty it can be marked with
%   a predicted outcome instead of 'empty'. A predicted
%   outcome is an integer.
%
%   The predictions are relative to state. If state
%   is x_next and the prediction is_outcome_a_loss( P)
%   and outcome_turn_count( P) == 2, it means X is
%   expected to lose (and O is expected to win) after
%   2 more moves by O.
%
%   There are never any predicted outcomes if
%   state is x_winner or o_winner since we already
%   know the winner. And there are no empty elements
%   to hold a prediction if state==cat_game.

% --------------------------------------------------------------
% init_board( )
%
%   Creates a board full of 'empty'.
%   Could also create a board full of undecided_outcome( ).
%   Calling predict_outcomes( Board, Xo) with an empty board
%   will get you a list of undecided_outcome( ) values.

init_board( ) ->
  { empty, empty, empty,
    empty, empty, empty,
    empty, empty, empty
  }.

% --------------------------------------------------------------
% fix_board_predicted_outcomes( Board, Xo_next )
%
%   Sets all the elements not marked x_mark or o_mark to a
%   predicted outcome (integer). The outcomes are calculated
%   assuming Xo_next (x_mark or o_mark) will be next marked on
%   the board.

fix_board_predicted_outcomes( Board, Xo ) ->
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  ?m_assert( not is_board_full( Board)),
  ?m_assert( not is_board_won( Board, x_mark)),
  ?m_assert( not is_board_won( Board, o_mark)),

  case is_board_empty( Board) of
    true  -> Board;
    false ->
      % Break up the board.
      {M1, M2, M3, M4, M5, M6, M7, M8, M9} =
        Board,

      % Find all the predicted outcomes.
      [P1, P2, P3, P4, P5, P6, P7, P8, P9] =
        predict_outcomes( Board, Xo),

      % Function to find the element value for the new board.
      Combo_fn =
        fun
          ( x_mark, collide ) -> x_mark;
          ( o_mark, collide ) -> o_mark;
          ( Mark  , Outcome ) ->
            ?m_assert( Mark /= x_mark),
            ?m_assert( Mark /= o_mark),
            ?m_assert( is_outcome_valid( Outcome)),
            Mark,
            Outcome
        end,

      % Create the new board.
      { Combo_fn( M1, P1), Combo_fn( M2, P2), Combo_fn( M3, P3),
        Combo_fn( M4, P4), Combo_fn( M5, P5), Combo_fn( M6, P6),
        Combo_fn( M7, P7), Combo_fn( M8, P8), Combo_fn( M9, P9)
      }
  end.

% --------------------------------------------------------------
% clear_board_predicted_outcomes( Board )
%
%   Returns a board where all spots that are not marked either
%   x_mark or o_mark will be marked 'empty' instead.
%   This clears all predicted outcomes from the board.

clear_board_predicted_outcomes(
    {M1, M2, M3, M4, M5, M6, M7, M8, M9} )
  ->
  Clear_fn =
    fun
      ( x_mark ) -> x_mark;
      ( o_mark ) -> o_mark;
      ( _      ) -> empty
    end,

  % Create the new board.
  { Clear_fn( M1), Clear_fn( M2), Clear_fn( M3),
    Clear_fn( M4), Clear_fn( M5), Clear_fn( M6),
    Clear_fn( M7), Clear_fn( M8), Clear_fn( M9)
  }.

% --------------------------------------------------------------
% get_board_best_predicted_position( Board )
%
%   Returns the position (1-9) of the best next move.
%
%   This relies on predicted outcomes stored in the board
%   elements. If no predicted outcomes are stored this returns
%   a random open position.

get_board_best_predicted_position( Board ) ->
  ?m_assert( not is_board_full( Board)),

  % Get the position of the best predicted outcome on the Board.
  % First we get a list of {Pos, Outcome} pairs from Board.
  %   zip: Changes board into list [ {1,M1}, {2,M2}, .. ].
  %   filter: Strips out all x_mark and o_mark marks.
  %   map: Changes 'empty' into undecided_outcome( ).
  %
  % We could use a list comprehension instead of lists:map(..):
  %   get_best_position_from_pair_list(
  %     [ { Pos, case Mark of
  %                empty -> undecided_outcome( ); _ -> Mark
  %              end
  %       }
  %       || {Pos, Mark} <- lists:zip(
  %                           lists:seq( 1, 9),
  %                           tuple_to_list( Board)),
  %          (Mark /= x_mark),
  %          (Mark /= o_mark) ]
  %
  get_best_position_from_pair_list(
    lists:map(
      fun
        ( {Pos, empty}     ) -> {Pos, undecided_outcome( )};
        ( Pos_outcome_pair ) -> Pos_outcome_pair
      end,
      lists:filter(
        fun
          ( {_, Mark} ) ->
            (Mark /= x_mark) andalso
            (Mark /= o_mark)
        end,
        lists:zip(
          lists:seq( 1, 9),
          tuple_to_list( Board))))).

% --------------------------------------------------------------
% get_best_position_from_pair_list( List_of_pairs )
%
%   Looks at all the pairs in a list and selects the one with
%   the best outcome. Returns the position from the best pair.
%
%   The pairs look like {Position, Outcome}.
%
%   We could add a small amount of randomness so that:
%     We occasionally pick the middle (5) even when we have
%       other choices available.
%     We occasionally pick a possibly losing move.
%     We occasionally pick a move that can cheat us of a win.
%
%   If we are making mistakes we should probably only make them
%   if the prediction is more than one move away. If we have an
%   immediate win, or if there is an immediate loss to block,
%   we should probably also pick that without mistakes.
%
%   If our best choice is the worst choice (lose next turn), and
%   we have more than one choice, we should:
%     forget about weeding out the middle, and
%     choose a move that at least blocks one 3-in-a-row.

get_best_position_from_pair_list( Pairs_all ) ->

  % Find the best outcome in the list of all outcomes.
  Outcome_best =
    lists:foldl(
      fun
        ( {_, Out_a}, Out_b ) ->
          case is_first_outcome_better( Out_a, Out_b) of
            true  -> Out_a;
            false -> Out_b
          end
      end,
      element( 2, hd( Pairs_all)),
      tl( Pairs_all)),

  % Find all the pairs with the best outcome.
  Pairs_best =
    lists:filter(
      fun ( {_, Out} ) -> Out == Outcome_best end,
      Pairs_all),

  % Return a position, the first element in the pair.
  element( 1,
    % Choose a pair from the list.
    % If there is only one choice left, return it.
    % There should always be at least one choice available.
    if
      tl( Pairs_best) == [] ->
        % A list has only one element if the tail is [].
        hd( Pairs_best);
      true ->
        % Return a random element from the list after removing
        % position 5 (if it is there).
        % Position 5 is the middle of the board, and the game
        % gets boring after the middle is marked.
        random_list_element( lists:keydelete( 5, 1, Pairs_best))
    end).

% --------------------------------------------------------------
% get_board_mark( Board, Position )
%
%   Returns the mark on the Board at Position.
%   A mark is either: x_mark, o_mark, empty, or a
%   predicted-outcome integer.

get_board_mark( Board, Pos ) -> element( Pos, Board).

% --------------------------------------------------------------
% mark_board( Board, Position, Mark )
%
%   Returns a new board with Mark at Position.
%   Use this to put new x_mark and o_marks on the board, and to
%   clear spots by marking them 'empty'.

mark_board(
  { _,_2,_3,_4,_5,_6,_7,_8,_9}, 1, M ) ->
  { M,_2,_3,_4,_5,_6,_7,_8,_9};
mark_board(
  {_1, _,_3,_4,_5,_6,_7,_8,_9}, 2, M ) ->
  {_1, M,_3,_4,_5,_6,_7,_8,_9};
mark_board(
  {_1,_2, _,_4,_5,_6,_7,_8,_9}, 3, M ) ->
  {_1,_2, M,_4,_5,_6,_7,_8,_9};
mark_board(
  {_1,_2,_3, _,_5,_6,_7,_8,_9}, 4, M ) ->
  {_1,_2,_3, M,_5,_6,_7,_8,_9};
mark_board(
  {_1,_2,_3,_4, _,_6,_7,_8,_9}, 5, M ) ->
  {_1,_2,_3,_4, M,_6,_7,_8,_9};
mark_board(
  {_1,_2,_3,_4,_5, _,_7,_8,_9}, 6, M ) ->
  {_1,_2,_3,_4,_5, M,_7,_8,_9};
mark_board(
  {_1,_2,_3,_4,_5,_6, _,_8,_9}, 7, M ) ->
  {_1,_2,_3,_4,_5,_6, M,_8,_9};
mark_board(
  {_1,_2,_3,_4,_5,_6,_7, _,_9}, 8, M ) ->
  {_1,_2,_3,_4,_5,_6,_7, M,_9};
mark_board(
  {_1,_2,_3,_4,_5,_6,_7,_8, _}, 9, M ) ->
  {_1,_2,_3,_4,_5,_6,_7,_8, M}.

% ------------------------------------------------------
% count_board_xo( Board )
%
%   Returns the number of X's and O's on the board.

count_board_xo( {_1,_2,_3,_4,_5,_6,_7,_8,_9} ) ->
  Num =
    fun
      ( x_mark ) -> 1;
      ( o_mark ) -> 1;
      ( _      ) -> 0
    end,
  Num( _1) + Num( _2) + Num( _3) +
  Num( _4) + Num( _5) + Num( _6) +
  Num( _7) + Num( _8) + Num( _9).

% ------------------------------------------------------
% is_board_empty( Board )
%
%   True if Board has no X or O marks.

is_board_empty( {_1,_2,_3,_4,_5,_6,_7,_8,_9} ) ->
  (_1 /= x_mark) andalso (_1 /= o_mark) andalso
  (_2 /= x_mark) andalso (_2 /= o_mark) andalso
  (_3 /= x_mark) andalso (_3 /= o_mark) andalso
  (_4 /= x_mark) andalso (_4 /= o_mark) andalso
  (_5 /= x_mark) andalso (_5 /= o_mark) andalso
  (_6 /= x_mark) andalso (_6 /= o_mark) andalso
  (_7 /= x_mark) andalso (_7 /= o_mark) andalso
  (_8 /= x_mark) andalso (_8 /= o_mark) andalso
  (_9 /= x_mark) andalso (_9 /= o_mark).

% ------------------------------------------------------
% is_board_full( Board )
%
%   True if every spot on Board is marked with X or O.

is_board_full( {_1,_2,_3,_4,_5,_6,_7,_8,_9} ) ->
  ((_1 == x_mark) orelse (_1 == o_mark)) andalso
  ((_2 == x_mark) orelse (_2 == o_mark)) andalso
  ((_3 == x_mark) orelse (_3 == o_mark)) andalso
  ((_4 == x_mark) orelse (_4 == o_mark)) andalso
  ((_5 == x_mark) orelse (_5 == o_mark)) andalso
  ((_6 == x_mark) orelse (_6 == o_mark)) andalso
  ((_7 == x_mark) orelse (_7 == o_mark)) andalso
  ((_8 == x_mark) orelse (_8 == o_mark)) andalso
  ((_9 == x_mark) orelse (_9 == o_mark)).

% --------------------------------------------------------------
% is_board_won( Board, Xo )
%
%   Predicate to test if Board is a winning board for Xo.
%   Returns 'true' or 'false'.
%
%   Board is a 9-tuple.
%
%   Xo is either x_mark or o_mark.

is_board_won( Board, Xo ) ->
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  is_board_won_detail( Board, Xo).

% Check all winning combinations.
% Check for 3-in-a-row:
is_board_won_detail( {X,X,X,_,_,_,_,_,_}, X ) -> true;
is_board_won_detail( {_,_,_,X,X,X,_,_,_}, X ) -> true;
is_board_won_detail( {_,_,_,_,_,_,X,X,X}, X ) -> true;

% Check for 3-in-a-column:
is_board_won_detail( {X,_,_,X,_,_,X,_,_}, X ) -> true;
is_board_won_detail( {_,X,_,_,X,_,_,X,_}, X ) -> true;
is_board_won_detail( {_,_,X,_,_,X,_,_,X}, X ) -> true;

% Check diagonals:
is_board_won_detail( {X,_,_,_,X,_,_,_,X}, X ) -> true;
is_board_won_detail( {_,_,X,_,X,_,X,_,_}, X ) -> true;

% No winner (yet):
is_board_won_detail( {_,_,_,_,_,_,_,_,_}, _ ) -> false.

% --------------------------------------------------------------
% Calculate Predicted Outcomes - predict_outcomes(..)
% --------------------------------------------------------------
%
%   Functions that, given a board and the next mover (X or O),
%   calculate the expected outcome of playing the next move at
%   each of the open spots on the board.
%
%   predict_outcomes( Board, Xo_next_move ) is the only
%   function "exported" from this section. The other functions
%   just implement the algorithm.
%
%   A predicted outcome states whether playing that spot on the
%   board will result in a win/loss/tie, and how many moves it
%   will take to win/lose. Presumably the player will want to
%   choose the move the wins the quickest or loses the slowest.
%   But lots of times there are several moves that lead to the
%   same predicted outcome. We could consider adding more info
%   to the outcomes to help us choose between them.
%
%     We could keep a score of how many winning/losing
%     opportunities are presented in the next board.
%     Right now we just look for the smartest next move, but
%     we could also add up all the winning next moves and
%     subtract all the losing next moves and keep that as
%     a tie-breaking value.
%
%     We could count all the paths leading to wins and losses
%     and use these values as tie-breakers. We could weight
%     the paths so that longer winning paths were less
%     valuable than shorter ones. Remember that each move
%     is a node in a tree that leads to other moves, and the
%     leaves of the game-tree are all wins, losses, and ties.
%
%     This is all pretty complicated though. We really have
%     an easier goal: if all our moves are "lose next turn"
%     (which is the worst possible choice), then we should pick
%     a move that at least blocks one three-in-a-row even if we
%     cannot block them all. We could choose a next move, and
%     then see what the other side's winning move is, and then
%     choose that move instead.

% --------------------------------------------------------------
% predict_outcomes( Board, Xo_init )
%
%   Returns a list of 9 results, one for each position on the
%   tic-tac-toe Board. A result is either 'collide' or a
%   predicted outcome, assuming we play Xo_init at that
%   position.
%
%   Board (9-tuple) - A tic-tac-toe board that is still being
%     played. It cannot be marked as a cat game or with a
%     winning three-in-a-row.
%
%   Xo_init - either x_mark or o_mark, depending on whether
%     it is X's or O's turn to move.

predict_outcomes( Board, Xo_init ) ->
  ?m_assert( (Xo_init == x_mark) or (Xo_init == o_mark)),

  % Calc Countdown so we search until we use up all the open
  % spots on the board. That is unless we find a winning or
  % losing board first.
  Countdown = 9 - count_board_xo( Board),
  ?m_assert( Countdown  > 0),
  ?m_assert( Countdown =< 9),

  % We start with undecided_outcome, but we never return it
  % without incrementing it at least once (with next_outcome).
  % We do, however, return undecided_outcome( ) if we run out
  % of open spots on the board, and thus predict a cat game.
  % But that "cat game" undecided_outcome( ) is not derived
  % from Init_outcome.
  Init_outcome = undecided_outcome( ),
  calc_all_outcomes( Board, Xo_init, Countdown, Init_outcome).

% --------------------------------------------------------------
% calc_all_outcomes( Board, Xo_next, Countdown, Outcome_start )
%
%   Given a Board and a next move (Xo_next), returns a list
%   of 9 predicted outcomes. The first outcome assumes Xo_next
%   is played at the first board position, the second outcome
%   in the return list assumes Xo_next is played at spot 2, etc.
%
%   Any spots that are already marked X or O on the board
%   will be marked with the 'collide' atom in the return list.
%
%   Xo_next - either x_mark or o_mark. Says which mark to put
%     down next on the board, an X or an O. This flips back
%     and forth between X and O as we look ahead and recurse
%     deeper.
%
%   Countdown - how many moves deep to explore. Stop when
%     this gets to zero.
%
%   Outcome_start - The outcome we'd have returned if the
%     board was already won. But since it's not won, we
%     increment Outcome_start at least once [using
%     next_outcome( Outcome_start)] before returning it.
%
%   Outcome_start tells us if Xo_next is the same as the Xo_init
%   we started with when predict_outcomes(..) was called. If
%   next_outcome( Outcome_start) is a winning outcome, then
%   Xo_next == Xo_init. Otherwise they are different.

calc_all_outcomes( Board, Xo, Countdown, Outcome_start ) ->
  % Check the parameters.
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  ?m_assert( Countdown > 0),
  ?m_assert( is_outcome_valid( Outcome_start)),

  % There are a couple ways to do this. The most straightforward
  % is to just use map (lists:map(..)) to build the list of 9
  % outcomes.
  %
  %   lists:map(
  %     fun( Pos ) ->
  %       given_move_predict_outcome(
  %         Board, Xo, Pos, Countdown, Outcome_start)
  %     end,
  %     lists:seq( 1, 9))
  %
  % Or you can use a list comprehension, which is a little more
  % elegant. Here are two equivalent ways to code it.
  %
  %   [ Out ||
  %     Pos <- lists:seq( 1, 9),
  %     Out <- [ given_move_predict_outcome(
  %                Board, Xo, Pos, Countdown, Outcome_start)
  %            ]
  %   ]
  %
  %   [ given_move_predict_outcome(
  %        Board, Xo, Pos, Countdown, Outcome_start)
  %     || Pos <- lists:seq( 1, 9) ]
  %
  % Since given_move_predict_outcome(..) is free of side-
  % effects, order of execution doesn't matter. So you can also
  % calculate all 9 elements of the list at the same time. Or
  % at least in separate processes. Order does matter, however,
  % in the result-list, so we have to restore order in the end.
  %
  % Note that these make a lot of processes - several hundred
  % thousand, all running at the same time. So you cannot run
  % the following bits of code on many systems.
  %
  %   % Multi-process solution using nested list comprehensions.
  %   % Uses child pids to order the results.
  %   Pid_parent = self( ),
  %   [ receive {Pid_child, Outcome_predicted} ->
  %       Outcome_predicted
  %     end
  %     || Pid_child <-
  %          [ spawn(
  %              % Send the results back to the parent process.
  %              % Also send self( ) (the child'd process ID) so
  %              % the parent can reassemble the list in order.
  %              fun( ) ->
  %                Pid_parent !
  %                  { self( ),
  %                    given_move_predict_outcome(
  %                      Board, Xo, Pos,
  %                      Countdown, Outcome_start)
  %                  }
  %              end)
  %            || Pos <- lists:seq( 1, 9)
  %          ]
  %   ]
  %
  %   % Multi-process solution using nested list comprehensions.
  %   % Uses Pos (board position, 1-9) to order the results.
  %   Pid_parent = self( ),
  %   [ receive {Pos, Outcome_predicted} ->
  %       Outcome_predicted
  %     end
  %     || Pos <-
  %        [ Pos
  %          || Pos <- lists:seq( 1, 9),
  %             is_pid(
  %               spawn(
  %                 fun( ) ->
  %                   Pid_parent !
  %                     { Pos,
  %                       given_move_predict_outcome(
  %                         Board, Xo, Pos,
  %                         Countdown, Outcome_start)
  %                     }
  %                 end)) ]]
  %
  %   % Same as above except using foreach(..) to scatter and
  %   % map(..) to gather.
  %   Pid_parent = self( ),
  %   Scatter_fn =
  %     fun( Pos ) ->
  %       spawn(
  %         fun( ) ->
  %           Pid_parent !
  %             { Pos,
  %               given_move_predict_outcome(
  %                 Board, Xo, Pos, Countdown, Outcome_start)
  %             }
  %         end)
  %     end,
  %   Gather_fn =
  %     fun( Pos ) ->
  %       receive { Pos, Outcome_predicted } ->
  %         Outcome_predicted
  %       end
  %     end,
  %   lists:foreach( Scatter_fn, lists:seq( 1, 9)),
  %   lists:map( Gather_fn, lists:seq( 1, 9))
  %
  % We'll stick to a simple solution to calc the 9 outcomes.
  [ given_move_predict_outcome(
        Board, Xo, Pos, Countdown, Outcome_start)
    || Pos <- lists:seq( 1, 9) ].

% --------------------------------------------------------------
% given_move_predict_outcome(
%     Board, Xo, Pos, Countdown, Outcome )
%
%   Predicts an outcome (win/loss/cat) given a move.
%
%   Returns a predicted outcome or 'collide'. The returned
%   outcome is relative to the Xo_init initially passed to
%   predict_outcome(..). So if the predicted outcome is
%   "win in 2" and Xo is not the same as Xo_init, then
%   we are predicting that Xo will actually lose in 2.
%
%   Xo is the X or O to mark on the Board.
%
%   Pos is which position (1-9) on the Board to mark.
%
%   Countdown tells us when to stop searching the play space.
%
%   Outcome is what we'd have returned if we'd won in the
%   last move. If we win in this move we're about to try,
%   we'll return next_outcome( Outcome).

given_move_predict_outcome( Board, Xo, Pos, Countdown, Outcome )
  ->
  % Check the parameters.
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  ?m_assert( (1 =< Pos) and (Pos =< 9)),
  ?m_assert( Countdown > 0),
  ?m_assert( is_outcome_valid( Outcome)),

  % Check to see if Pos on Board is available to be marked.
  case get_board_mark( Board, Pos) of
    x_mark -> collide;
    o_mark -> collide;
    _ ->
      Next_board     = mark_board( Board, Pos, Xo),
      Next_countdown = Countdown - 1,
      Next_outcome   = next_outcome( Outcome),
      after_move_predict_outcome(
        Next_board, Xo, Next_countdown, Next_outcome)
  end.

% --------------------------------------------------------------
% after_move_predict_outcome( Board, Xo, Countdown, Outcome )
%
%   Called immediately after Xo has been marked on the Board.
%
%   Countdown tells us when to stop searching for wins/loses.
%   It will be zero if Board has no more unmarked spots.
%
%   Outcome is returned if the last Xo move was a winning move.
%
%   Returns a predicted outcome.
%   If the last move was a winner, return the Outcome passed in.

after_move_predict_outcome( Board, Xo, Countdown, Outcome ) ->
  % Check the parameters.
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  ?m_assert( Countdown >= 0),
  ?m_assert( is_outcome_valid( Outcome)),
  ?m_assert( not is_outcome_undecided( Outcome)),

  case is_board_won( Board, Xo) of
    true  -> Outcome;
    false ->
      case Countdown == 0 of
        true  -> undecided_outcome( );
        false ->
          try_all_moves_best_outcome( Board,
            if Xo == x_mark -> o_mark;
               Xo == o_mark -> x_mark
            end,
            Countdown, Outcome)
      end
  end.

% --------------------------------------------------------------
% try_all_moves_best_outcome( Board, Xo, Countdown, Outcome )
%
%   Applies all possible next moves to Board, looking for
%   the best one. Board must have at least one open position.
%   Predicts the best outcome (for Xo) after trying Xo in all
%   the open positions on the Board.
%
%   Board is a non-winning board with at least one unplayed
%   spot available for the next Xo mark.
%
%   Xo is the next X or O to mark on the Board.
%
%   Countdown tells us when to stop searching for wins/loses.
%
%   Outcome is predicted outcome we would have returned if the
%   last move had been a winner. Since Board is not a winner,
%   we will apply at least one more mark and transform
%   Outcome into next_outcome( Outcome) at least one more time
%   before returning.

try_all_moves_best_outcome( Board, Xo, Countdown, Outcome ) ->
  % Check the parameters.
  ?m_assert( (Xo == x_mark) or (Xo == o_mark)),
  ?m_assert( Countdown > 0),
  ?m_assert( is_outcome_valid( Outcome)),
  ?m_assert( not is_outcome_undecided( Outcome)),

  % Filter out all occurances of 'collide'. There should always
  % be at least one outcome that is not 'collide'.
  [ First_outcome | Remaining_outcomes ] =
    lists:filter(
      fun( X ) -> X /= collide end, 
      calc_all_outcomes( Board, Xo, Countdown, Outcome)),

  % Given this move, ask what all the outcomes of all the next
  % moves are. Assume the other player will pick the outcome
  % that is best for him, which will be the move that is worst
  % for us.
  %
  % The returned outcomes are all relative to the Xo_init that
  % we passed in to predict_outcomes(..) to start this search.
  % So if Xo (the mark we just put down on the board) is the
  % same as Xo_init, we want to return the best move for us.
  % But since we get a list of outcomes for all the possible
  % next moves by the other player, we have to assume that he
  % will choose the move that is worst for us.
  %
  % On the other hand, if Xo is not Xo_init, we assume the next
  % other player is Xo_init and will select the move that is
  % best for Xo_init and worst for us.
  %
  % We can tell if Xo is the same as Xo_init because
  % is_outcome_a_win( Outcome) will be true.
  %
  lists:foldl(
    case is_outcome_a_win( Outcome) of
      true  ->
        % Xo is the same as Xo_init.
        % Collect the worst outcome from all the next moves
        % because that is the next move the other player
        % will choose (we assume).
        fun
          ( A, B ) ->
            case is_first_outcome_better( B, A ) of
              true  -> A;
              false -> B
            end
        end;
      false ->
        % Xo is not the same as Xo_init.
        % Collect the best outcome, because it is best for
        % Xo_init and Xo_init moves next.
        fun
          ( A, B ) ->
            case is_first_outcome_better( A, B ) of
              true  -> A;
              false -> B
            end
        end
    end,
    First_outcome,
    Remaining_outcomes).

% --------------------------------------------------------------
% Predicted Outcomes
% --------------------------------------------------------------
%
%   Abstraction and definition of predicted_outcome.
%   Predicted_outcome is an enumerated type.
%
%   Predicted outcomes are integers (negative and positive).
%   They are always predictions for the mark whose turn it is,
%   so if X is moving next and the prediction is "lose in 1",
%   it means that X is expected to lose (and O to win) when
%   O moves next.
%
%   Predicted outcomes have these values:
%      0  - No prediction. You can get this if you do a
%           limited search for a winner and can draw no
%           conclusions. But since we always search the
%           entire game space, 0 means we expect a cat
%           game.
%
%     -1  - The next mark can win the game.
%     -2  - The current-turn mark will win on the 2nd turn
%           after this. So if it's X's turn, we expect a move
%           by X, followed by an O, followed by the winning X.
%     -3  - The current-turn mark can win in 3 turns.
%
%     +1  - The current-turn mark will lose in this words.
%           Say it is X's turn, the X will play first,
%           followed by a winning move by O.
%     +2  - If it's X's turn, the moves will be:
%             X, O, X, and O (winning move, X loses).
%
%   Suggestions:
%     Right now we treat "unknown outcome" the same as
%     "predict outcome to be a tie". Both are the value 0.
%     It'd probably be an improvement to separate these
%     and choose "predict tie" over "unknown" while still
%     considering "unknown" a better choice than "predict a
%     loss in 4 moves".
%
%     We can go farther and keep track of how far we've
%     searched before comming up with "unknown". So we might
%     have "completely unknown", which means we haven't looked
%     ahead at all, and "unknown after searching 2 deep" which
%     means searching 2 moves forward in the game space did not
%     reveal either a win or loss. Maybe it's clearer to think
%     "neither win nor loss predicted" instead of "unknown".
%
%     If we are faced with a board where we'll lose no matter
%     what (the other side can make three-in-a-row two different
%     ways), the automatic mover will just choose a random move
%     right now. But it'd be better if it choose to at least
%     block one of the three-in-a-rows.
%
%     So another thing we could add to the predicted outcomes
%     is how many losing paths are blocked by the next move,
%     and how many winning paths are opened up. So even if we
%     were bound to lose we could still make the computer look
%     like it's fighting the lost cause to the bitter end.
%
%     We try to avoid automatically choosing the center spot
%     right now unless it's clearly the best move. This is
%     because it makes the game boring. An interesting game is
%     one where there are more potential (and longer) paths to
%     victory. A boring game is where all the moves are forced.
%     We could come up with a tie-breaking factor in the
%     predicted outcome that steered us away from boring
%     choices (when all other factors were equal).

% --------------------------------------------------------------
% is_outcome_valid( Predicted_outcome )
%
%   These integers are small because tic-tac-toe is so limited.
%   -5 really never happens -- it'd be a prediction for a
%   winner 9 half-moves from now.

% This is only used in asserts.
-ifndef( NODEBUG ).
is_outcome_valid( P ) ->
  is_integer( P) andalso (P >= -5) andalso (P =< 4).
-endif.

% --------------------------------------------------------------
% undecided_outcome( )
% is_outcome_undecided( P )
%
%   Undecided means we search for a win/loss outcome and did
%   not find one. Since we always search all the way to a full
%   board in tic-tac-toe, undecided_outcome( ) is the same
%   as predicting a cat game.

undecided_outcome( ) -> 0.
is_outcome_undecided( P ) -> P == 0.

% --------------------------------------------------------------
% is_outcome_a_win(  P )
% is_outcome_a_loss( P )
%
%   Says whether we are predicting a win or a loss.

is_outcome_a_win(  P ) -> P < 0.
is_outcome_a_loss( P ) -> P > 0.

% --------------------------------------------------------------
% outcome_turn_count( P )
%
%   Integer saying in how many turns we are predicting a win or
%   loss. Zero if we're predicting neither.

outcome_turn_count( P ) ->
  ?m_assert( is_outcome_valid( P)),
  abs( P ).

% --------------------------------------------------------------
% next_outcome( P )
%
%   Returns this sequence of integers, starting at undecided:
%     0 (undecided), -1 (win), 1 (loss), -2, 2, -3, 3 ..etc..

next_outcome( P ) ->
  ?m_assert( is_outcome_valid( P)),
  ?m_confirm( is_outcome_valid,
     - ( if P < 0 -> P;
            true  -> P + 1
         end
       )
  ).

% --------------------------------------------------------------
% is_first_outcome_better( A, B )
%
%   This is a less-than, not a less-than-or-equal test.
%   If A and B are equal, this returns false.
%
%   Outcomes from best to worst are:
%     -1 - win next move
%     -2 - win in 2 moves
%     -3 - win in 3 moves
%        .. etc ..
%      0 - tie game (or no prediction)
%     +4 - lose in 4
%     +3 - lose in 3
%     +2 - lose in 2
%     +1 - lose immediately
%
%   What's best for X is always worst for O, and vice versa.

is_first_outcome_better( A, B ) ->
  ?m_assert( is_outcome_valid( A)),
  ?m_assert( is_outcome_valid( B)),

  % Negative numbers are better since they predict a win.
  % -1 is the best since it predicts an immediate win.
  % 0 means a tie game, so it is better than a positive
  % integer which means a loss.
  % 3 is better than 1 since 1 means an immediate loss.
  case { A < 0, B < 0 } of
    { true , false } -> true ;
    { false, true  } -> false;
    { true , true  } -> A > B;
    { false, false } ->
    if
      B == 0 -> false;
      A == 0 -> true ;
      true   -> A > B
    end
  end.

% --------------------------------------------------------------
% User Input - get_next_move(..)
% --------------------------------------------------------------
%
%   Asks the user for the next move. Also prints help.
%
%   The user choices are:
%     quit      - quit playing
%     help      - describe the user options
%
%     new_game  - start a new game,
%                   even if the current one is not finished.
%
%     simple    - show the board again with a simple display
%                   that shows only X's and O's. Change the
%                   print option.
%     number    - change print option and show board with
%                   numbers in blank spots.
%     predict   - change print option and show board with
%                   predicted outcomes described in the
%                   blank spots.
%                   Also shows numbers in the blank spots.
%
%     automatic - have the computer select the next move.
%     skip      - skip the next move, so if it was X's turn
%                   skip that and make it O's turn instead.
%
%     {mark, Position}  - select Position (1-9) for the next
%                           X or O move, whoever's turn it is.
%     {erase, Position} - erase the X or O at Position. If an
%                           X is erased it becomes X's turn,
%                           and the same for O.
%
%   This section "exports" one function: get_next_move( Game ).
%   It returns one of the above commands, except it handles
%   help itself and never returns 'help'.
%
%   All returns are validated and guaranteed to be OK.
%   The atoms 'quit' 'new_game' 'simple' 'number' and 'predict'
%   are always OK and can be returned at any time.
%   'automatic' and 'skip' are only returned if the board is
%   in play, which means it is neither won nor cat.
%   {mark,Pos} is only returned if the board is in play and
%   the Pos (1-9) is not marked X or O.
%   {empty,Pos} is only returned if the board is marked X or
%   O at Pos (1-9), so it is never returned for an empty board.
%   {empty,Pos} can be returned if the board is won or cat.

% --------------------------------------------------------------
% get_next_move( Game )
% get_next_move( State, Board )
%
%   Returns the next user command from default standard input.
%   Only returns valid commands that are consistent with Board
%   and State.
%
%   Returns one of the following 8 commands. If Position (1-9)
%   is part of the command, it will have been validated.
%     quit  new_game
%     simple  number  predict
%     automatic  skip
%     {mark, Position}
%     {erase, Position}

get_next_move( Game ) ->
  get_next_move( get_game_state( Game), get_game_board( Game)).

get_next_move( cat_game, Board ) ->
  write_line( "Cat game."),
  ask_for_command( cat_game, Board);

get_next_move( x_winner, Board ) ->
  write_line( "X is the winner."),
  ask_for_command( x_winner, Board);

get_next_move( o_winner, Board ) ->
  write_line( "O is the winner."),
  ask_for_command( o_winner, Board);

get_next_move( x_next, Board ) ->
  write_line( "It is X's turn to move."),
  ask_for_command( x_next, Board);

get_next_move( o_next, Board ) ->
  write_line( "It is O's turn to move."),
  ask_for_command( o_next, Board).

% --------------------------------------------------------------
% ask_for_command( State, Board )

ask_for_command( State, Board ) ->
  Command =
    translate_to_command(
      get_user_input(
        "What do you want to do (h=help, q=quit)? ")),

  % Useful letter in some of the messages below.
  Xo_letter =
    case State of
      x_next -> $X;
      o_next -> $O;
      _ -> $#
    end,

  case Command of
    % Quit and new_game are always valid commands.
    quit      -> quit;
    new_game  -> new_game;

    % Change the print option, which is always OK.
    simple    ->
      write_line(
        "Setting print option to show a simple board."),
      simple;
    number    ->
      write_line(
        "Setting print option to show position numbers."),
      number;
    predict   ->
      write_line(
        "Setting print option to show predicted outcomes."),
      predict;

    % Move commands are invalid on won and cat games.
    automatic ->
      case is_state_consistent_with_move( State ) of
        true  ->
          write_line(
            "Automatically selecting ~c's next move.",
            Xo_letter),
          automatic;
        false ->
          ask_for_command( State, Board)
      end;

    % Skip is like a move command.
    skip      ->
      case is_state_consistent_with_move( State ) of
        true  ->
          write_line( "Skipping ~c's next turn.", Xo_letter),
          skip;
        false ->
          ask_for_command( State, Board)
      end;

    % Move command can only be issued if game not yet won or
    % cat, and if move position isn't already marked X or O.
    {mark, Pos} ->
      case is_state_consistent_with_move( State, Board, Pos) of
        true  ->
          write_line( "Marking ~c at position ~w.",
            Xo_letter, Pos),
          Command;
        false ->
          ask_for_command( State, Board)
      end;

    % Erase command that is not valid on an empty board.
    % It is also invalid is Pos is not marked X or O.
    {erase, Pos} ->
      case is_board_consistent_with_erase( Board, Pos) of
        true  ->
          Xo_erase =
            case get_board_mark( Board, Pos) of
              x_mark -> $X;
              o_mark -> $O
            end,
          write_line( "Erasing the ~c at position ~w.",
            Xo_erase, Pos),
          Command;
        false ->
          ask_for_command( State, Board)
      end;

    % Help is handled here. Print help and ask again.
    help ->
      print_help( State, Board),
      ask_for_command( State, Board);

    % Fall through that prints help and asks again.
    _ ->
      write_line( "Unrecognized command."),
      print_help( State, Board),
      ask_for_command( State, Board)
  end.

% --------------------------------------------------------------
% get_user_input( Prompt )
%
%   Asks the user for a command. After the user types something
%   and hits return, we strip the line-feed from the end of the
%   string, and any spaces from the front and back.

get_user_input( Prompt ) ->
  string:strip(   % remove spaces from front and back
    string:strip( % remove line-feed from the end
      io:get_line( Prompt), right, $\n)).

% --------------------------------------------------------------
% is_state_consistent_with_move( State, Board, Position )
% is_state_consistent_with_move( State )

is_state_consistent_with_move( State, Board, Pos ) ->
  case is_state_consistent_with_move( State) of
    false -> false;
    _ ->
      Mark = get_board_mark( Board, Pos),
      if
        Mark /= x_mark, Mark /= o_mark -> true;
        true ->
          write_string( "Invalid request - spot "),
          write_arg( Pos),
          write_string( " is already marked "),
          write_line(
            case Mark of
              x_mark -> "X.";
              o_mark -> "O."
            end),
          case {State, Mark} of
            {x_next, x_mark} -> ok;
            {o_next, o_mark} -> ok;
            _                ->
              write_string( "To change it to "),
              write_string(
                case State of
                  x_next -> "X";
                  o_next -> "O"
                end),
              write_string( " erase it first with the 'e"),
              write_arg( Pos),
              write_line( "' command.")
          end,
          false
      end
  end.

is_state_consistent_with_move( State ) ->
  case State of
    % You can only make move if the game is not won or cat.
    x_next -> true;
    o_next -> true;
    _ ->
      write_string( "Invalid request - "),
      write_line(
        case State of
          x_winner -> "X has already won.";
          o_winner -> "O has already won.";
          cat_game -> "The game over in a tie."
        end),
      write_line( "You cannot add more marks to the board."),
      false
  end.

% --------------------------------------------------------------
% is_board_consistent_with_erase( Board, Position )

is_board_consistent_with_erase( Board, Pos ) ->
  Mark = get_board_mark( Board, Pos),
  case Mark of
    x_mark -> true;
    o_mark -> true;
    _ ->
      write_string( "Invalid request - spot "),
      write_arg( Pos),
      write_string( " is not marked X or O"),
      write_line( " and so cannot be erased."),
      false
  end.

% --------------------------------------------------------------
% translate_to_command( String )
%
%   Return values:
%     quit; new_game;
%     simple; number; predict;
%     automatic; skip;
%     {mark, Pos}; {erase, Pos}
%     false

% Quit the game.
translate_to_command( [Q|_] )
  when Q == $q; Q == $Q
  ->
  quit;

% Print help.
translate_to_command( [H|_] )
  when H == $h; H == $H
  ->
  help;

% Start a new game.
translate_to_command( [G|_] )
  when G == $g; G == $G
  ->
  new_game;

% Print a simple board and set print option to 'simple'.
translate_to_command( [B|_] )
  when B == $b; B == $B
  ->
  simple;

% Set print options to show the board with numbers in
% the empty spots, and then print the board again.
translate_to_command( [N|_] )
  when N == $n; N == $N
  ->
  number;

% Print the big board with predictions.
% Set print options to show the board with predicted outcomes
% and numbers in the empty spots, and print the board again.
translate_to_command( [P|_] )
  when P == $p; P == $P
  ->
  predict;

% Let the computer select the next move automatically.
translate_to_command( [A|_] )
  when A == $a; A == $A
  ->
  automatic;

% Skip this turn for the current xo mark.
% This is the same as saying if it's X's turn, make it O's
% turn instead, and vice versa.
translate_to_command( [S|_] )
  when S == $s; S == $S
  ->
  skip;

% Let the computer select the next move automatically.
translate_to_command( [Digit] )
  when Digit >= $1, Digit =< $9
  ->
  Pos = Digit - $0,
  ?m_assert( (1 =< Pos) and (Pos =< 9)),
  {mark, Pos};

% Erase an X or O now on the board.
% Returns either {erase, Pos} or false the entry was not valid.
translate_to_command( [E | Digit_str] )
  when E == $e; E == $E
  ->
  case string:strip( Digit_str) of
    [Pos_char]
        when is_integer( Pos_char),
        $1 =< Pos_char, Pos_char =< $9
      ->
        Pos = Pos_char - $0,
        ?m_assert( (1 =< Pos) and (Pos =< 9)),
        {erase, Pos};
    _ ->
        false
  end;

% Catch all case. Returns false whenever the user enters
% h, help, or anything that was not understood.
translate_to_command( _ )
  ->
  false.

% --------------------------------------------------------------
% print_help( State, Board )

print_help( State, Board ) ->
  write_line( ),
  write_line( "Please enter one of the following:"),
  write_line( "  q - quit"),
  write_line( "  h - help, show this message"),
  write_line( "  g - start a new game"),
  write_line( "  b - show a simple board"),
  write_line( "  n - show the board with open spots numbered"),
  write_line( "  p - show a board with predicted outcomes"),

  fun
    ( ok     ) -> ok;
    ( Xo_str ) ->
      Print_helper =
        fun( Prefix ) ->
          write_string( Prefix),
          write_string( Xo_str),
          write_line( " next move")
        end,
      write_line(   "  1-9 (a single digit)"     ),
      Print_helper( "    - choose "              ),
      Print_helper( "  a - automatically choose "),
      Print_helper( "  s - skip "                )
  end( case State of
         x_next -> "X's";
         o_next -> "O's";
         _      -> ok
       end),

  case is_board_empty( Board) of
    true  -> ok;
    false ->
      write_line( "  e1-e9 ('e' followed by a single digit)"),
      write_line( "    - erase an X or O already on the board")
  end,

  write_line( ).

% --------------------------------------------------------------
% Board Display - print_board(..)
% --------------------------------------------------------------
%
%   This section "exports" the function print_board( Game ).
%
%   Prints the tic-tac-toe board to standard IO.
%   The printed board looks like this (with predictions):
%
%                   []     OOOOO     []   XXX   XXX   
%      1   WINNING  []   OOO   OOO   []     XX XX     
%            MOVE!  []  OOO     OOO  []      XXX      
%                   []   OOO   OOO   []     XX XX     
%                   []     OOOOO     []   XXX   XXX   
%    ===============##===============##===============
%                   []   XXX   XXX   []   XXX   XXX   
%      2  Loses in  []     XX XX     []     XX XX     
%      three moves  []      XXX      []      XXX      
%       after this  []     XX XX     []     XX XX     
%                   []   XXX   XXX   []   XXX   XXX   
%    ===============##===============##===============
%         OOOOO     []     OOOOO     []
%       OOO   OOO   []   OOO   OOO   []  9   Leads to
%      OOO     OOO  []  OOO     OOO  []      CAT game
%       OOO   OOO   []   OOO   OOO   []
%         OOOOO     []     OOOOO     []

% --------------------------------------------------------------
% print_board( Game )
% print_board( Board, Option )
%
%   Writes a big-display board to standard IO.
%
%   Option controls what we show in empty cells.
%   It is one of the following:
%     simple   - leave empty cells blank
%     number   - show position number in empty cell
%     predict  - show position and predicted outcome

print_board( Game ) ->
  print_board(
    get_game_board( Game), get_game_print_option( Game)).

print_board( Board, Option ) ->
  ?m_assert(
    (Option == simple) or
    (Option == number) or
    (Option == predict)),

  Option_adjusted =
    case (Option == predict) andalso is_board_empty( Board) of
      true  -> number;
      false -> Option
    end,

  write_line( ),
  print_row( Board, Option_adjusted, 1),
  print_hori_divider( ),
  print_row( Board, Option_adjusted, 4),
  print_hori_divider( ),
  print_row( Board, Option_adjusted, 7),
  write_line( ).

% --------------------------------------------------------------
% print_hori_divider( )
% print_vert_divider( )

print_hori_divider( ) ->
  write_string( "===============##"),
  write_string( "===============##"),
  write_line(   "===============").

print_vert_divider( ) ->
  write_string( "[]").

% --------------------------------------------------------------
% print_row( Board, Option, Position )
% print_row( Option, Pos, Mark1, Mark2, Mark3, Index )
% print_row( Option, Pos, Mark, Index )

print_row( Board, Option, Pos ) ->
  M1 = get_board_mark( Board, Pos + 0),
  M2 = get_board_mark( Board, Pos + 1),
  M3 = get_board_mark( Board, Pos + 2),
  lists:foreach(
    fun ( Index ) ->
      print_row( Option, Pos, M1, M2, M3, Index)
    end,
    lists:seq( 1, 5)).

print_row( Option, Pos, M1, M2, M3, Index ) ->
  print_row( Option, Pos + 0, M1, Index),
  print_vert_divider( ),
  print_row( Option, Pos + 1, M2, Index),
  print_vert_divider( ),
  print_row( Option, Pos + 2, M3, Index),
  write_line( ).

print_row( Option, Pos, M, Index ) ->
  case M of
    x_mark -> print_cell_x( Index);
    o_mark -> print_cell_o( Index);
    _      ->
      case Option of
        simple  ->
          print_cell_empty( );
        number  ->
          print_cell_number( Pos, Index);
        predict ->
          case M of
            empty ->
              print_cell_number( Pos, Index);
            _     ->
              % M must be an Outcome.
              ?m_assert( is_outcome_valid( M)),
              print_cell_predict_outcome( M, Pos, Index)
          end
      end
  end.

% --------------------------------------------------------------
% print_cell_x( Index )
% print_cell_o( Index )
% print_cell_empty( )
% print_cell_number( Position, Index )
%
%   Index goes from 1 thru 5.

print_cell_x( Index ) ->
  write_string(
    if
      Index == 1; Index == 5 -> "   XXX   XXX   ";
      Index == 2; Index == 4 -> "     XX XX     ";
      Index == 3             -> "      XXX      "
    end).

print_cell_o( Index ) ->
  write_string(
    if
      Index == 1; Index == 5 -> "     OOOOO     ";
      Index == 2; Index == 4 -> "   OOO   OOO   ";
      Index == 3             -> "  OOO     OOO  "
    end).

print_cell_empty( ) ->
  write_space( 15).

print_cell_number( Pos, Index ) ->
  if
    Index == 3 ->
      write_space( 7),
      write_arg( Pos),
      write_space( 7);
    true ->
      write_space( 15)
  end.

% --------------------------------------------------------------
% print_cell_predict_outcome( Outcome, Position, Index )

print_cell_predict_outcome( Outcome, Pos, Index ) ->
  if
    Index == 1;
    Index == 5 ->
      write_space( 15);
    true ->
      write_space( 2),
      case Index of
        2 -> print_cell_predict_outcome_1( Outcome, Pos);
        3 -> print_cell_predict_outcome_2( Outcome);
        4 -> print_cell_predict_outcome_3( Outcome)
      end,
      write_space( 2)
  end.

% --------------------------------------------------------------
% print_cell_predict_outcome_1( Outcome, Position )
% print_cell_predict_outcome_2( Outcome )
% print_cell_predict_outcome_3( Outcome )

print_cell_predict_outcome_1( Outcome, Pos ) ->
  write_arg( Pos),
  write_space( ),
  write_string(
    case is_outcome_undecided( Outcome) of
      true  -> get_print_string_leads_to( );
      false ->
    case is_outcome_a_win( Outcome) of
      true  ->
        case outcome_turn_count( Outcome) of
          1 -> get_print_string_winning(  );
          _ -> get_print_string_wins_in(  )
        end;
      false ->
    case is_outcome_a_loss( Outcome) of
      true  ->
        case outcome_turn_count( Outcome) of
          1 -> get_print_string_loses(    );
          _ -> get_print_string_loses_in( )
        end
    end end end).

print_cell_predict_outcome_2( Outcome ) ->
  write_string(
    case is_outcome_undecided( Outcome) of
      true  -> get_print_string_cat_game(    );
      false ->
    case is_outcome_a_win( Outcome) of
      true  ->
        case outcome_turn_count( Outcome) of
          1 -> get_print_string_move(        );
          2 -> get_print_string_next_turn(   );
          3 -> get_print_string_three_turns( );
          4 -> get_print_string_four_turns(  );
          5 -> get_print_string_five_turns(  )
        end;
      false ->
    case is_outcome_a_loss( Outcome) of
      true  ->
        case outcome_turn_count( Outcome) of
          1 -> get_print_string_after_this(  );
          2 -> get_print_string_two_turns(   );
          3 -> get_print_string_three_turns( );
          4 -> get_print_string_four_turns(  )
        end
    end end end).

print_cell_predict_outcome_3( Outcome ) ->
  write_string(
    case
      is_outcome_undecided( Outcome) orelse
      (outcome_turn_count( Outcome) == 1)
    of
      true  -> get_print_string_blank( );
      false -> get_print_string_after_this( )
    end).

% --------------------------------------------------------------
% Strings used to construct messages

get_print_string_leads_to(    ) -> " Leads to".
get_print_string_winning(     ) -> "  WINNING".
get_print_string_loses(       ) -> "    Loses".
get_print_string_wins_in(     ) -> "  Wins in".
get_print_string_loses_in(    ) -> " Loses in".

get_print_string_cat_game(    ) -> "   CAT game".
get_print_string_move(        ) -> "      MOVE!".
get_print_string_next_turn(   ) -> "  next turn".
get_print_string_two_turns(   ) -> "  two turns".
get_print_string_three_turns( ) -> "three turns".
get_print_string_four_turns(  ) -> " four turns".
get_print_string_five_turns(  ) -> " five turns".
get_print_string_after_this(  ) -> " after this".
get_print_string_blank(       ) -> "           ".

% --------------------------------------------------------------
% Simple String Output
% --------------------------------------------------------------
%
%   These are covers for calls to io:fwrite(..).

% --------------------------------------------------------------
% write_line( )
% write_line( Str)
% write_line( Str, Arg)
% write_line( Str, Arg1, Arg2)
% write_string( Str)
% write_string( Str, Arg)
% write_string( Str, Arg1, Arg2)
% write_space( )
% write_space( N)
% write_arg( Arg)

write_line( ) ->
  io:nl( ).

write_line( Str ) ->
  write_string( Str),
  write_line( ).

write_line( Str, Arg ) ->
  write_string( Str, Arg),
  write_line( ).

write_line( Str, Arg1, Arg2 ) ->
  write_string( Str, Arg1, Arg2),
  write_line( ).

write_string( Str ) ->
  io:fwrite( Str).

write_string( Str, Arg ) ->
  io:fwrite( Str, [Arg]).

write_string( Str, Arg1, Arg2 ) ->
  io:fwrite( Str, [Arg1, Arg2]).

write_space( ) ->
  write_string( " ").

write_space( 0 ) ->
  ok;
write_space( N ) when N > 0 ->
  write_space( ),
  write_space( N - 1).

write_arg( Arg ) ->
  write_string( "~w", Arg).

% --------------------------------------------------------------
% Random Utilities
% --------------------------------------------------------------

% --------------------------------------------------------------
% random_list_element( List )
%
%   Returns a single element from List.
%   List must have at least one element.

random_list_element( List ) ->
  if
    List      == [] -> erlang:error( badarg);
    tl( List) == [] -> hd( List);
    true ->
      Count = length( List),
      Index = random:uniform( Count),
      lists:nth( Index, List)
  end.

% --------------------------------------------------------------
% randomize_random_seed( )
%
%   Seed the random generator with unpredictable numbers.
%
%   Uses now( ), which returns the current time in this form:
%     {Mega_seconds, Seconds, Micro_seconds}
%
%   Maybe these integers aren't the best seeds since
%   Mega-seconds doesn't change much and Micro-seconds is
%   always a multiple of 1000 on my machine.
%
%   There are other sources of unpredictable numbers we could
%   use as seeds:
%
%     statistics( wall_clock) ->
%         {Total_milliseconds, Elapsed_milliseconds}
%     Total milliseconds seems a good candidate.
%
%     statistics( garbage_collection) ->
%         {Number_of_gcs, Words_reclaimed, 0}
%     Words_reclaimed is a good unpredictable integer.
%
%   random:seed(..) returns the previous seed value (3-tuple
%   of integers), so we could restore the seed value in case
%   some other system is counting on it.
%   Remember that random:seed(..) returns the atom 'undefined'
%   if the seed has never been set before.

randomize_random_seed( ) ->

  % Get a seed of 3 psuedo-random looking integers.
  {Meg_secs, Secs , Micro_secs} = now( ),

  % Set the seed.
  random:seed( Meg_secs, Secs, Micro_secs).