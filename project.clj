(defproject regina "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [potemkin "0.4.3"]
                 [loco "0.3.1"]]
  :profiles {:dev {:dependencies [[org.clojure/math.numeric-tower "0.0.4"]
                                  [org.clojure/test.check "0.9.1-SNAPSHOT"]]}}
  :jvm-opts ["-Xmx12g"
             "-XX:+UseConcMarkSweepGC"
             "-XX:+UseParNewGC"
             "-XX:+CMSParallelRemarkEnabled"
             "-XX:+AggressiveOpts"
             "-XX:+UseFastAccessorMethods"
             "-XX:+CMSClassUnloadingEnabled"
             "-XX:-OmitStackTraceInFastThrow"
             ])
