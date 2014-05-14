type answer = Sat | Unsat | Unknown | Error of string
type solver = Standard | NLSat | Both


let log_Z3_input = false
let solver = Both

let info = ref None
let log = ref ""
let stack = ref 0

let is_started () = None != !info

let stop () =
	match !info with
		| None -> failwith "Z3 not running"
		| Some(pid, c_in, c_out) ->
			if Unix.getpid () = pid then begin
				let process_status = Unix.close_process (c_in, c_out) in
				begin match process_status with
					| Unix.WEXITED 0 -> ()
					| Unix.WEXITED exit_code -> Printf.printf "Z3 exited with exit code %i\n" exit_code
					| Unix.WSIGNALED signal -> Printf.printf "Z3 was killed by a signal %i\n" signal
					| Unix.WSTOPPED signal -> Printf.printf "Z3 was stopped by a signal %i\n" signal
				end ;
				if (process_status <> Unix.WEXITED 0) || log_Z3_input then begin
					print_endline "\n\nZ3 LOG\n" ;
					print_endline !log
				end ;
				if !stack != 0 then Printf.printf "\nERROR: STACK = %i\n\n" !stack
			end ;
			info := None

let get_out_channel () =
	match !info with
		| None -> failwith "Z3 not running"
		| Some (_, _, c_out) -> c_out

let get_in_channel () =
	match !info with
		| None -> failwith "Z3 not running"
		| Some (_, c_in, _) -> c_in

let read () =
	let c_in = get_in_channel () in
	match input_line c_in with
		| "unsat" -> Unsat
		| "sat" -> Sat
		| "unknown" -> Unknown
		| error -> Error error

let write str =
	let c_out = get_out_channel () in
	output_string c_out str ;
	output_char c_out '\n' ;
	flush c_out ;
	log := !log ^ str ^ "\n"

let check_sat () =
	match solver with
		| Standard ->
				write "(check-sat)" ;
				read ()
		| NLSat ->
				write "(check-sat-using qfnra-nlsat)" ;
				read ()
		| Both ->
				write "(check-sat)" ;
				match read () with
					| Unknown ->
							write "(check-sat-using qfnra-nlsat)" ;
							read ()
					| answer -> answer

let start () =
	if not (is_started ()) then begin
		let c_in, c_out = Unix.open_process "z3 -smt2 -in -t:4" in
		info := Some (Unix.getpid (), c_in, c_out) ;
		write "(set-option :global-decls false)" ;
		at_exit stop
	end

let push () = write "(push)" ; incr stack
let pop () = write "(pop)\n" ; decr stack

let push_pop fn =
	push () ;
	let result = 
		try
			fn ()
		with e -> pop () ; raise e
	in
	pop () ;
	result

