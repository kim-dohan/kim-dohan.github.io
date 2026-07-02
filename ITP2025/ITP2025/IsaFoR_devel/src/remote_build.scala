object Remote_Build
{
  import isabelle._

  /* settings */


  val REMOTE_BUILD_REMOTE_HOST = "REMOTE_BUILD_REMOTE_HOST"
  val REMOTE_BUILD_REMOTE_BASE = "REMOTE_BUILD_REMOTE_BASE"
  val REMOTE_BUILD_SSH_PROXY = "REMOTE_BUILD_SSH_PROXY"
  val REMOTE_BUILD_SSH_CONFIG  = "REMOTE_BUILD_SSH_CONFIG"

  val settings = List(REMOTE_BUILD_REMOTE_HOST, REMOTE_BUILD_REMOTE_BASE, REMOTE_BUILD_SSH_PROXY, REMOTE_BUILD_SSH_CONFIG)

  def show_settings(): String = cat_lines(settings.map(c =>
    c + "=" + quote(Isabelle_System.getenv(c))))

  private def rsync_cmdline(remote_host: String,
      sources: List[String], target: String, filters: List[String] = Nil,
      remote_shell: String = "ssh"): String =
    "rsync -avzc --progress " +
    "--rsh=" + quote(remote_shell) + " " +
    filters.map("--filter '" + _ + "'").mkString(" ") + " " +
    Bash.strings(sources.map(remote_host + ":" + _)) + " " +
    target

  def apply(args: List[String])
  {
    var remote_base_dir = Isabelle_System.getenv(REMOTE_BUILD_REMOTE_BASE) match {
      case "" => Path.explode("~")
      case dir => Path.explode(dir)
    }
    var dirs: List[Path] = Nil
    var opts: List[String] = Nil
    var remote_host = Isabelle_System.getenv(REMOTE_BUILD_REMOTE_HOST)
    var incremental = false
    var verbose = false

    var proxy: String = ""
    var proxy_port: Int = 2222

    def parse_proxy(p: String) = p.split(":") match {
      case Array(h, p) => proxy = h; proxy_port = p.toInt
      case Array(h) => proxy = h
    }

    Isabelle_System.getenv(REMOTE_BUILD_SSH_PROXY) match {
      case "" =>
      case p => parse_proxy(p)
    }

    var ssh_config_file: String = Isabelle_System.getenv(REMOTE_BUILD_SSH_CONFIG)

    val getopts = Getopts(s"""
Usage: isabelle remote_build [OPTIONS] SESSIONS ...

  Options are:
    -B DIR       base directory for remote Isabelle installations (default:
                 $$REMOTE_BUILD_REMOTE_BASE, or if former not set ~)
    -d DIR       include session directory
    -r HOST      remote host name (default: $$REMOTE_BUILD_REMOTE_HOST)
    -o OPTION    add option for remote isabelle call, e.g., -o -d -o '$$ISAFOR'
    -i           incremental: only synchronize heap images that are newly built
                 on the remote host (default: synchronize all session heaps
                 together with their ancestors)
    -P PROXY     connect to remote host via proxy jump; PROXY may either be
                 a HOST or a specification HOST:PORT (default:
                 $$REMOTE_BUILD_SSH_PROXY on port 2222)
    -v           be verbose
    -c FILE      use FILE as SSH config file

  Build and copy heap images, observing implicit settings:

""" + Library.prefix_lines("  ", show_settings()) + "\n",
      "B:" -> (arg => remote_base_dir = Path.explode(arg)),
      "d:" -> (arg => {
        dirs = dirs ::: List(Path.explode(arg))
        if (arg.startsWith("$"))
          // use same session directory variables also on REMOTE
          opts = opts ::: "-d" :: List(arg)
      }),
      "r:" -> (arg => remote_host = arg),
      "o:" -> (arg => opts = opts ::: List(arg)),
      "i"  -> (arg => incremental = true),
      "P:" -> (arg => parse_proxy(arg)),
      "v"  -> (arg => verbose = true),
      "c:" -> (arg => ssh_config_file = arg))

    val select_sessions = getopts(args)
    if (select_sessions.isEmpty) getopts.usage()
    if (remote_host.isEmpty) getopts.usage()

    var options = Options.init()
    if (ssh_config_file == "" || Path.explode(ssh_config_file).is_file)
      options = options.string.update("ssh_config_file", ssh_config_file)
    else
      Output.error_message(s"ssh_config_file '$ssh_config_file' is not a file")

    val progress = new Console_Progress

    val sessions = Sessions.load_structure(options, dirs = dirs)

    if (!proxy.isEmpty) {
      if (verbose)
        progress.echo("Connecting to proxy " + proxy)
      val ssh_tunnel = SSH.init_context(options).open_session(proxy)
      ssh_tunnel.port_forwarding(local_port = proxy_port, remote_host = remote_host, remote_port = 22, ssh_close = true)
    }

    progress.echo("Connecting to " + remote_host)

    val ssh_session =
      if (!proxy.isEmpty) SSH.init_context(options).open_session(host = "localhost", port = proxy_port)
      else SSH.init_context(options).open_session(remote_host)
    using(ssh_session)(ssh =>
    {

      val remote_isabelle_home: Path =
        remote_base_dir +
          Path.explode(
            proper_string(Isabelle_System.getenv("ISABELLE_IDENTIFIER")).getOrElse("isabelle"))

      def remote_isabelle(arg: String,
          progress_stdout: String => Unit = (_: String) => (),
          progress_stderr: String => Unit = (_: String) => ()): Process_Result = {
        val cmd = ssh.bash_path(remote_isabelle_home + Path.explode("bin/isabelle")) + " " + arg
        if (verbose)
          progress.echo("*remote* " + cmd)
        ssh.execute(
          cmd,
          progress_stdout = progress_stdout,
          progress_stderr = progress_stderr)
      }

      val remote_output_dir: Path =
        Path.explode(remote_isabelle("getenv -b ISABELLE_HOME_USER").check.out) +
        Path.explode("heaps") +
        Path.explode(remote_isabelle("getenv -b ML_IDENTIFIER").check.out)

      val store = Sessions.store(options)

      def build_files(s: String) = List(Path.explode(s), store.database(s), store.log_gz(s))

      val build_deps = sessions.build_graph.all_preds(select_sessions).reverse

      val target = store.output_dir

      val (rsync_host, rsync_rsh) =
        if (!proxy.isEmpty) ("localhost", "ssh -p " + proxy_port)
        else (remote_host, "ssh")

      def rsync_callback(line: String): Unit = {
        progress.echo(line)
        if (line.startsWith("Finished ")) {
          val session = space_explode(' ', line)(1)
          if (build_deps.contains(session)) {
            for (file <- build_files(session)) {
              Isabelle_System.mkdirs(target + file.dir)
              val cmd = rsync_cmdline(
                remote_host = rsync_host,
                sources = List(ssh.bash_path(remote_output_dir + file)),
                target = File.bash_path(target + file),
                remote_shell = rsync_rsh)
               progress.echo(cmd)
              Isabelle_System.bash(cmd, redirect = true, progress_stdout = progress.echo(_)).check
            }
          }
        }
      }

      remote_isabelle("build -v " + Bash.strings(opts) + " -b " + Bash.strings(select_sessions),
        progress_stdout = rsync_callback(_),
        progress_stderr = progress.echo(_)).check

      if (!incremental) {
        val file_filters = build_deps.flatMap(build_files(_).map("+ /" + File.bash_path(_)))
        val cmd = rsync_cmdline(
          remote_host = rsync_host,
          sources = List(ssh.bash_path(remote_output_dir) + "/"),
          target = File.bash_path(target),
          filters = "+ /log/" ::  file_filters ::: List("- *"),
          remote_shell = rsync_rsh)
        progress.echo(cmd)
        Isabelle_System.bash(cmd, redirect = true, progress_stdout = progress.echo(_)).check
      }

      /*for {
        session <- sessions.build_graph.all_preds(select_sessions).reverse
        file <- List(Path.explode(session), store.database(session), store.log_gz(session))
      } {
        val target = store.output_dir
        Isabelle_System.mkdirs(target + file.dir)
        Isabelle_System.bash(
          "rsync -avz " +
            Bash.string(remote_host + ":") + ssh.bash_path(remote_output_dir + file) + " " +
            File.bash_path(target + file),
          redirect = true,
          progress_stdout = progress.echo(_)).check
      }*/
    })
  }

  def main(args: Array[String])
  {
    Command_Line.tool0 { apply(args.toList) }
  }
}
