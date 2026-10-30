package compiler.setup

object EnvironmentVariables {
  
  val licorneHome: String = "LICORNE_HOME"
  
  def envGetLicorneHome(displayErrorIfNotSet: Boolean): Option[String] = {
    val envVar = System.getenv(licorneHome)
    if (envVar == null) {
      if (displayErrorIfNotSet) {
        System.err.println(s"environment variable $licorneHome is not set")
      }
      None
    } else Some(envVar)
  }

}
