open Util

let main () =
  bracket
    ~acquire:begin fun () ->
      open_out "/tmp/primate.log"
    end
    ~release:begin fun oc ->
      close_out oc
    end
    begin fun oc ->
      let fmt = Format.formatter_of_out_channel oc in
      Logs.set_reporter (Logs.format_reporter ~app:fmt ~dst:fmt ()) ;
      Logs.set_level (Some Logs.Debug) ;

      Log.debug (fun m -> m "Registering signals!") ;
      catch_signals posix_signals ;
      Log.debug (fun m -> m "Done!") ;
      Broker.start ()
    end

let () =
  main ()
