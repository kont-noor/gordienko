  require 'rubygems'
  require 'sinatra'
  require 'sinatra/content_for'
  require 'haml'
  require 'sass'
  require 'uri'

  #enable :sessions

class Main < Sinatra::Base

  set :app_file, __FILE__
  set :root, Proc.new { app_file && File.expand_path(File.dirname(app_file)) }
  set :public, Proc.new { root && File.join(root, 'public') }
  set :static, Proc.new { public && File.exist?(public) }
	
  before do
    content_type :html, 'charset' => 'utf-8'
  end

  def with_layout(template, options={}) 
    #erb(template, options.merge(:layout => :'/header'))
    haml template, :locals => {:active => template}.merge(options)
  end

  def captcha_pass?
    session = params[:captcha_session].to_i
    answer = params[:captcha_answer].gsub(/\W/, '')
    open("http://captchator.com/captcha/check_answer/#{session}/#{answer}").read.to_i.nonzero? rescue false
  end

  def captcha_session
    @captcha_session ||= rand(9000) + 1000
  end

  def captcha_tags
    {
      :session => captcha_session,
      :image => "http://captchator.com/captcha/image/#{captcha_session}"
    }
  end

  get '/css/screen.css' do
   content_type :css
   sass :stylesheet # overridden
  end

  get '/' do
    with_layout :index
  end
  
  get '/consultations' do
    with_layout :consultations
  end

  get '/news' do
    with_layout :news
  end

  get '/guest' do
    with_layout :guest
  end

  get '/information' do
    with_layout :information
  end

  get '/contacts' do
    with_layout :contacts, {:answer => nil}.merge(captcha_tags)
  end

  post '/contacts/sending' do
    if captcha_pass?
      answer = 'Капча правильная!'
    else
      answer = 'Неверно введена капча'
    end
    with_layout :contacts, {:answer => answer}.merge(captcha_tags)
  end

  helpers Sinatra::ContentFor
end